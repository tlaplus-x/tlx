//! The value store operations of the compiled tier (`ir::RefOp`), shared
//! by all executors: the closure executor calls `run` directly, JIT and C
//! code through the host callback `ref_op` (ABI v5), which comes here too.
//! Each operation is the store method of the same name
//! (`tlx_layout::store`), so all executors compute the same handles and fail in
//! the same cases.

use std::sync::atomic::{AtomicU64, Ordering};

use tlx_layout::store::{self, RefOpError, Store};

use crate::ir::RefOp;
use crate::types::Typing;

/// An argument of an operation: a word (a handle, an integer, a Boolean
/// as 0/1) or the words of an encoding (`RefOp::FromEnc`).
#[derive(Clone, Copy)]
pub(crate) enum RArg<'a> {
    W(u64),
    E(&'a [u64]),
}

impl RArg<'_> {
    #[inline]
    fn w(self) -> u64 {
        match self {
            RArg::W(x) => x,
            RArg::E(_) => panic!("value store operation: an encoding where a word was expected"),
        }
    }
}

/// Operations run, by the closure executor and by native code (statistics,
/// counted with relaxed atomics only when `-stats` is on).
pub(crate) static CALLS: [AtomicU64; 2] = [AtomicU64::new(0), AtomicU64::new(0)];

/// Run `op` on `args` (in its representations), writing the result to
/// `out` (one word, or `ToEnc`'s encoding). An error is a TLC error or a
/// case the store leaves to the interpreter (`RefOpError::Eval`), or a full
/// store.
pub(crate) fn run(s: &Store, typing: &Typing, op: &RefOp, args: &[RArg], out: &mut [u64]) -> Result<(), RefOpError> {
    use RefOp as O;
    let w = |i: usize| args[i].w();
    out[0] = match op {
        O::Domain => s.domain(w(0))?,
        O::Apply => s.apply(w(0), w(1))?,
        O::Select => match s.select(w(0), w(1))? {
            Some(i) => i as u64,
            None => -1i64 as u64,
        },
        O::ValueAt => {
            let (f, i) = (w(0), w(1) as usize);
            if s.node(f).is_none_or(|n| i >= n.fcn_len()) {
                return Err(RefOpError::Eval);
            }
            s.value_at(f, i)
        }
        O::SetAt => {
            let (f, i) = (w(0), w(1) as usize);
            if s.node(f).is_none_or(|n| i >= n.fcn_len()) {
                return Err(RefOpError::Eval);
            }
            s.set_at(f, i, w(2))?
        }
        O::Single => s.single(w(0), w(1))?,
        O::Merge => s.merge(w(0), w(1))?,
        O::Member => s.member(w(0), w(1))? as u64,
        O::InDomain => s.in_domain(w(0), w(1))? as u64,
        O::Field(name) => s.field(w(0), *name)?,
        O::Cardinality => s.cardinality(w(0))? as u64,
        O::Len => s.len(w(0))? as u64,
        O::Append => s.append(w(0), w(1))?,
        O::Head => s.head(w(0))?,
        O::Tail => s.tail(w(0))?,
        O::Tuple => {
            let es: Vec<u64> = args.iter().map(|a| a.w()).collect();
            s.tuple(&es)?
        }
        O::Record(names) => {
            let fs: Vec<(tlx_value::Sym, u64)> = names.iter().zip(args).map(|(n, a)| (*n, a.w())).collect();
            s.record(&fs)?
        }
        O::Eq => store::eq_tlc(s, w(0), w(1))? as u64,
        O::FromInt => store::int_handle(w(0) as i64).ok_or(RefOpError::Eval)?,
        O::FromBool => store::bool_handle(w(0) != 0),
        O::ToInt => store::as_int(w(0)).ok_or(RefOpError::Eval)? as u64,
        O::ToBool => store::as_bool(w(0)).ok_or(RefOpError::Eval)? as u64,
        O::FromEnc(sid) => {
            let RArg::E(words) = args[0] else { return Err(RefOpError::Eval) };
            // SAFETY: verified IR fixes sid and the operand span; these
            // initialized words come from that shape's encoder/generated
            // code, with published active handles from this model's tables.
            let v = unsafe { typing.node(*sid).decode_unchecked(words) };
            s.freeze(&v)?
        }
        O::ToEnc(sid) => {
            let v = s.thaw(w(0));
            let n = typing.words(*sid) as usize;
            typing.node(*sid).encode(&v, &mut out[..n]).map_err(|_| RefOpError::Eval)?;
            return Ok(());
        }
    };
    Ok(())
}

/// Count one operation (`-stats`; `native`: called by JIT or C code).
#[inline]
pub(crate) fn count(native: bool) {
    if tlx_runtime::stats::on() {
        CALLS[native as usize].fetch_add(1, Ordering::Relaxed);
    }
}

/// The value store operations a native library calls (`host->ref_op`,
/// ABI v5): every distinct (operation, arity) of a verified program, in
/// the order of a fixed traversal, so that C and the JIT, and the host,
/// number them alike. The table's text is part of the C source (so of the
/// native cache key) and its hash of `tlx_spec_info`.
pub struct RefOpTable {
    ops: Vec<(RefOp, usize)>,
    ids: std::collections::HashMap<(RefOp, usize), u32>,
    /// Per operation: the layout of `FromEnc`'s / `ToEnc`'s encoding.
    nodes: Vec<Option<tlx_layout::LayoutNode>>,
    store: store::StoreRef,
    typing: Typing,
    text: String,
    hash: u64,
    /// Per operation: calls and failures (`-stats` only).
    counts: Vec<[AtomicU64; 2]>,
}

impl RefOpTable {
    /// The table of `prog` (None if it has no value store operations).
    pub fn of(prog: &crate::verify::Program<'_>) -> Option<std::sync::Arc<RefOpTable>> {
        let typing = prog.typing();
        let store = typing.ref_store()?;
        let mut ops: Vec<(RefOp, usize)> = Vec::new();
        let mut ids = std::collections::HashMap::new();
        let mut add = |e: &crate::ir::Expr| {
            if let crate::ir::ExprKind::RefOp { op, args } = &*e.kind {
                let key = (op.clone(), args.len());
                ids.entry(key.clone()).or_insert_with(|| {
                    ops.push(key);
                    ops.len() as u32 - 1
                });
            }
        };
        fn walk(e: &crate::ir::Expr, f: &mut dyn FnMut(&crate::ir::Expr)) {
            f(e);
            e.for_each_child(&mut |c| walk(c, f));
        }
        let stmt = |s: &crate::ir::Stmt, f: &mut dyn FnMut(&crate::ir::Expr)| s.for_each_expr_deep(&mut |e| walk(e, f));
        if let Some(i) = prog.init() {
            stmt(&i.body, &mut add);
        }
        for a in prog.actions().iter().flatten() {
            stmt(&a.body, &mut add);
        }
        for p in prog.predicates().iter().chain(prog.transitions()) {
            walk(&p.body, &mut add);
        }
        for f in &typing.funcs {
            walk(&f.body, &mut add);
        }
        if ops.is_empty() {
            return None;
        }
        let nodes = ops
            .iter()
            .map(|(op, _)| match op {
                RefOp::FromEnc(sid) | RefOp::ToEnc(sid) => Some(typing.node(*sid).clone()),
                _ => None,
            })
            .collect();
        let mut text = String::new();
        for (i, (op, n)) in ops.iter().enumerate() {
            let shape = match op {
                RefOp::FromEnc(sid) | RefOp::ToEnc(sid) => format!(" {:?}", typing.shape(*sid)),
                _ => String::new(),
            };
            text += &format!("{i}: {} {n}{shape}\n", op_text(op));
        }
        let hash = {
            use std::hash::Hasher;
            let mut h = tlx_base::hash::StableHasher::new();
            h.write(text.as_bytes());
            h.finish()
        };
        let counts = ops.iter().map(|_| [AtomicU64::new(0), AtomicU64::new(0)]).collect();
        Some(std::sync::Arc::new(RefOpTable { ops, ids, nodes, store, typing: typing.clone(), text, hash, counts }))
    }

    /// The id of `op` with `n` arguments (None: not in the table).
    pub(crate) fn id(&self, op: &RefOp, n: usize) -> Option<u32> {
        self.ids.get(&(op.clone(), n)).copied()
    }

    /// The canonical text of the table (one line per operation).
    pub(crate) fn text(&self) -> &str {
        &self.text
    }

    /// The native calls and failures of each operation that was called
    /// (`-stats`), most calls first.
    pub(crate) fn report(&self) -> String {
        let mut rows: Vec<(u64, u64, usize)> = self
            .counts
            .iter()
            .enumerate()
            .map(|(i, c)| (c[0].load(Ordering::Relaxed), c[1].load(Ordering::Relaxed), i))
            .filter(|r| r.0 > 0)
            .collect();
        rows.sort_by_key(|r| (std::cmp::Reverse(r.0), r.2));
        let mut out = String::new();
        for (calls, failed, i) in rows {
            let (op, n) = &self.ops[i];
            out += &format!("  {calls:>12} calls {failed:>9} failed  {} ({n} args)\n", op_text(op));
        }
        out
    }
}

/// An operation as text independent of interning (names, not symbol ids).
fn op_text(op: &RefOp) -> String {
    match op {
        RefOp::Field(s) => format!("Field({})", s.as_str()),
        RefOp::Record(ns) => format!("Record({})", ns.iter().map(|s| s.as_str()).collect::<Vec<_>>().join(",")),
        op => format!("{op:?}"),
    }
}

impl tlx_native::mixed::RefOps for RefOpTable {
    fn len(&self) -> u32 {
        self.ops.len() as u32
    }

    fn hash(&self) -> u64 {
        self.hash
    }

    unsafe fn run(&self, id: u32, args: *const u64, out: *mut u64) -> bool {
        let (op, n) = &self.ops[id as usize];
        let node = self.nodes[id as usize].as_ref();
        // SAFETY: the library is generated for this verified operation table:
        // args is non-null, u64-aligned, and readable for n initialized words
        // in one allocation for this call (including a non-null empty span).
        let raw = unsafe { std::slice::from_raw_parts(args, *n) };
        let rargs: Vec<RArg> = match (op, node) {
            (RefOp::FromEnc(_), Some(node)) => {
                // SAFETY: FromEnc's verified signature makes raw[0] a
                // non-null aligned pointer to node.words() initialized words
                // in one allocation, live for this call and disjoint from out.
                vec![RArg::E(unsafe { std::slice::from_raw_parts(raw[0] as usize as *const u64, node.words()) })]
            }
            _ => raw.iter().map(|w| RArg::W(*w)).collect(),
        };
        let words = match (op, node) {
            (RefOp::ToEnc(_), Some(node)) => node.words(),
            _ => 1,
        };
        count(true);
        let ok = if matches!(op, RefOp::ToEnc(_)) {
            // SAFETY: the signature provides an aligned, exclusively writable
            // output span of words u64s, disjoint from args and any FromEnc
            // input. It can be an uninitialized native stack slot: initialize
            // before forming a Rust slice. ToEnc's encoder writes all words.
            unsafe { out.write_bytes(0, words) };
            // SAFETY: the preceding raw write initialized the entire live
            // output allocation; this slice does not escape the call.
            let out = unsafe { std::slice::from_raw_parts_mut(out, words) };
            run(&self.store, &self.typing, op, &rargs, out).is_ok()
        } else {
            // Scalar outputs need no initialization of the native slot. Keep
            // the safe executor's result in a local word, then publish it only
            // on success (failed operations leave the output untouched).
            let mut word = [0];
            let ok = run(&self.store, &self.typing, op, &rargs, &mut word).is_ok();
            if ok {
                // SAFETY: out owns room for the one-word result for this call;
                // a raw write accepts uninitialized storage, without a borrow.
                unsafe { out.write(word[0]) };
            }
            ok
        };
        // NativeLib::ref_op_cb runs this method under catch_unwind; a panic
        // is resumed after the generated call returns, never across the C ABI.
        if tlx_runtime::stats::on() {
            let c = &self.counts[id as usize];
            c[0].fetch_add(1, Ordering::Relaxed);
            if !ok {
                c[1].fetch_add(1, Ordering::Relaxed);
            }
        }
        ok
    }

    fn elems(&self, set: u64) -> Option<&[u64]> {
        self.store.set_elems(set)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::mem::MaybeUninit;
    use std::sync::Arc;
    use tlx_layout::{Layout, Shape};
    use tlx_native::mixed::RefOps;
    use tlx_value::Value;

    #[test]
    fn native_refops_accept_uninitialized_output_and_preserve_failure() {
        let store = store::StoreRef::new(1 << 20);
        // Two 63-bit bounded ints span two packed words (`[3 << 1, 4 << 1]`),
        // exercising multi-word uninitialized `ToEnc` output initialization.
        let shape = Shape::Tuple(vec![Shape::Int { lo: 0, hi: i64::MAX }; 2].into());
        let mut typing = Typing::new(Arc::new(Layout::new(vec![Shape::Ref(store.clone())])));
        let sid = typing.id(&shape);
        let expected_node = typing.node(sid).clone();
        let table = RefOpTable {
            ops: vec![(RefOp::FromInt, 1), (RefOp::ToEnc(sid), 1)],
            ids: Default::default(),
            nodes: vec![None, Some(expected_node.clone())],
            store,
            typing,
            text: String::new(),
            hash: 0,
            counts: (0..2).map(|_| [AtomicU64::new(0), AtomicU64::new(0)]).collect(),
        };
        let mut scalar = MaybeUninit::<u64>::uninit();
        // SAFETY: valid table ids, initialized one-word args and exclusive
        // aligned output slots of the exact signature size; none overlap.
        unsafe {
            assert!(table.run(0, [3].as_ptr(), scalar.as_mut_ptr()));
            assert_eq!(scalar.assume_init(), store::int_handle(3).unwrap());
            let mut unchanged = 17;
            assert!(!table.run(0, [i64::MAX as u64].as_ptr(), &mut unchanged));
            assert_eq!(unchanged, 17);
            let tuple = Value::tuple(vec![Value::Int(3), Value::Int(4)]);
            let mut expected = [0u64; 2];
            expected_node.encode(&tuple, &mut expected).unwrap();
            let value = table.store.freeze(&tuple).unwrap();
            let mut encoded = MaybeUninit::<[u64; 2]>::uninit();
            assert!(table.run(1, [value].as_ptr(), encoded.as_mut_ptr().cast()));
            assert_eq!(encoded.assume_init(), expected);
        }
    }
}
