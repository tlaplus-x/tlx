//! Memoization of constant-level operator applications in constant
//! contexts (ASSUME, constant definitions, the cfg): a pure operator's value
//! depends only on its arguments, and constant-level tests often apply the
//! same operator to the same arguments many times (MCReachabilityTest:
//! `ReachableFrom(T)` for every pair `S, T \in SUBSET Nodes`). TLC does not
//! memoize; the values are the same, so results are unchanged.
//!
//! Per thread, keyed by the interpreter, the definition, KeepLazy and the
//! argument values compared by representation (not TLC equality: `<<>>`
//! and the empty function of an enumerated domain behave differently).
//! Only small, fully built arguments (no lazy values) are keys, and only
//! small values are kept. Errors are not memoized. A definition whose lookups rarely hit is no longer
//! memoized on that thread; the table is cleared when it is full.

use std::borrow::Borrow;
use std::cell::RefCell;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use tlx_base::hash::FxMap;
use tlx_sema::hir::{DefId, Span};
use tlx_value::Value;

use crate::apply::Cow;
use crate::env::{Binding, Env};
use crate::error::EResult;
use crate::eval::Ctx;
use crate::interp::Interp;

/// Most entries per thread (cleared when full).
const MAX_ENTRIES: usize = 1 << 16;
/// Most nodes of the arguments of a memoized application.
const MAX_ARG_NODES: usize = 256;
/// Most nodes of a memoized value (a lazy value counts as one).
pub(crate) const MAX_VALUE_NODES: usize = 4096;
/// After this many lookups of a definition, it is no longer memoized if
/// fewer than 1 in `MIN_HIT_RATIO` hit.
const PROBATION: u32 = 1024;
const MIN_HIT_RATIO: u32 = 8;

/// Trait-object lookup key so `TABLE.entries` can be probed from borrowed
/// `&[&Value]` arguments without allocating a `Vec<Value>` or cloning args.
trait MemoKey {
    fn uid(&self) -> u64;
    fn def(&self) -> DefId;
    fn keep_lazy(&self) -> bool;
    fn arg_len(&self) -> usize;
    fn arg(&self, i: usize) -> &Value;
}

fn hash_key<H: Hasher>(k: &dyn MemoKey, state: &mut H) {
    k.uid().hash(state);
    k.def().hash(state);
    k.keep_lazy().hash(state);
    for i in 0..k.arg_len() {
        hash_repr(k.arg(i), state);
    }
}

fn eq_key(a: &dyn MemoKey, b: &dyn MemoKey) -> bool {
    a.uid() == b.uid()
        && a.def() == b.def()
        && a.keep_lazy() == b.keep_lazy()
        && a.arg_len() == b.arg_len()
        && (0..a.arg_len()).all(|i| same(a.arg(i), b.arg(i)))
}

struct Key {
    uid: u64,
    def: DefId,
    keep_lazy: bool,
    args: Vec<Value>,
}

impl MemoKey for Key {
    #[inline]
    fn uid(&self) -> u64 {
        self.uid
    }
    #[inline]
    fn def(&self) -> DefId {
        self.def
    }
    #[inline]
    fn keep_lazy(&self) -> bool {
        self.keep_lazy
    }
    #[inline]
    fn arg_len(&self) -> usize {
        self.args.len()
    }
    #[inline]
    fn arg(&self, i: usize) -> &Value {
        &self.args[i]
    }
}

struct BorrowedKey<'a> {
    uid: u64,
    def: DefId,
    keep_lazy: bool,
    args: &'a [&'a Value],
}

impl MemoKey for BorrowedKey<'_> {
    #[inline]
    fn uid(&self) -> u64 {
        self.uid
    }
    #[inline]
    fn def(&self) -> DefId {
        self.def
    }
    #[inline]
    fn keep_lazy(&self) -> bool {
        self.keep_lazy
    }
    #[inline]
    fn arg_len(&self) -> usize {
        self.args.len()
    }
    #[inline]
    fn arg(&self, i: usize) -> &Value {
        self.args[i]
    }
}

impl<'a> Borrow<dyn MemoKey + 'a> for Key {
    fn borrow(&self) -> &(dyn MemoKey + 'a) {
        self
    }
}

impl Hash for Key {
    fn hash<H: Hasher>(&self, state: &mut H) {
        hash_key(self, state);
    }
}

impl PartialEq for Key {
    fn eq(&self, o: &Key) -> bool {
        eq_key(self, o)
    }
}

impl Eq for Key {}

impl Hash for dyn MemoKey + '_ {
    fn hash<H: Hasher>(&self, state: &mut H) {
        hash_key(self, state);
    }
}

impl PartialEq for dyn MemoKey + '_ {
    fn eq(&self, o: &Self) -> bool {
        eq_key(self, o)
    }
}

impl Eq for dyn MemoKey + '_ {}

/// A hash of `v` consistent with `same`: by representation, so that an
/// interval costs O(1) (a fingerprint enumerates it, e.g. `1..2147483647`).
fn hash_repr<H: Hasher>(v: &Value, state: &mut H) {
    std::mem::discriminant(v).hash(state);
    match v {
        Value::Bool(b) => b.hash(state),
        Value::Int(i) => i.hash(state),
        Value::Str(s) | Value::ModelValue(s) => s.hash(state),
        Value::Interval(lo, hi) => (lo, hi).hash(state),
        Value::Set(es) | Value::Tuple(es) => {
            es.len().hash(state);
            es.iter().for_each(|e| hash_repr(e, state));
        }
        Value::Record(fs) => fs.iter().for_each(|(k, e)| {
            k.hash(state);
            hash_repr(e, state);
        }),
        Value::Fcn(ps, _) => ps.iter().for_each(|(k, e)| {
            hash_repr(k, state);
            hash_repr(e, state);
        }),
        // (Not keys: see `plain`.)
        Value::LazySet(_) | Value::LazyFcn(_) => {}
    }
}

/// Equal values with the same representation.
fn same(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Bool(x), Value::Bool(y)) => x == y,
        (Value::Int(x), Value::Int(y)) => x == y,
        (Value::Str(x), Value::Str(y)) | (Value::ModelValue(x), Value::ModelValue(y)) => x == y,
        (Value::Interval(a, b), Value::Interval(c, d)) => a == c && b == d,
        (Value::Set(x), Value::Set(y)) | (Value::Tuple(x), Value::Tuple(y)) => {
            x.len() == y.len() && x.iter().zip(y.iter()).all(|(p, q)| same(p, q))
        }
        (Value::Record(x), Value::Record(y)) => x.len() == y.len() && x.iter().zip(y.iter()).all(|(p, q)| p.0 == q.0 && same(&p.1, &q.1)),
        (Value::Fcn(x, dx), Value::Fcn(y, dy)) => {
            dx == dy && x.len() == y.len() && x.iter().zip(y.iter()).all(|(p, q)| same(&p.0, &q.0) && same(&p.1, &q.1))
        }
        _ => false,
    }
}

/// Whether `v` is fully built (no lazy value) and small enough to be part
/// of a key; counts its nodes against `budget`.
pub(crate) fn plain(v: &Value, budget: &mut usize) -> bool {
    if *budget == 0 {
        return false;
    }
    *budget -= 1;
    match v {
        Value::Bool(_) | Value::Int(_) | Value::Str(_) | Value::ModelValue(_) | Value::Interval(..) => true,
        Value::Set(es) | Value::Tuple(es) => es.iter().all(|e| plain(e, budget)),
        Value::Record(fs) => fs.iter().all(|(_, e)| plain(e, budget)),
        Value::Fcn(ps, _) => ps.iter().all(|(k, e)| plain(k, budget) && plain(e, budget)),
        Value::LazySet(_) | Value::LazyFcn(_) => false,
    }
}

/// Whether `v` has at most `budget` nodes (a lazy value counts as one).
pub(crate) fn small(v: &Value, budget: &mut usize) -> bool {
    if *budget == 0 {
        return false;
    }
    *budget -= 1;
    match v {
        Value::Set(es) | Value::Tuple(es) => es.iter().all(|e| small(e, budget)),
        Value::Record(fs) => fs.iter().all(|(_, e)| small(e, budget)),
        Value::Fcn(ps, _) => ps.iter().all(|(k, e)| small(k, budget) && small(e, budget)),
        _ => true,
    }
}

/// Whether borrowed arguments `args` can be a key.
fn keyable_refs(args: &[&Value]) -> bool {
    let mut budget = MAX_ARG_NODES;
    args.iter().all(|a| plain(a, &mut budget))
}

#[derive(Default)]
struct Table {
    entries: FxMap<Key, Value>,
    /// Per (interpreter, definition): lookups and hits.
    stats: FxMap<(u64, DefId), (u32, u32)>,
}

thread_local! {
    static TABLE: RefCell<Table> = RefCell::new(Table::default());
}

/// Result of a borrowed memo lookup.
enum Lookup {
    Hit(Value),
    Miss,
    Disabled,
}

/// Whether memoization of `def` has been disabled on this thread after
/// failing probation (fewer than 1 in `MIN_HIT_RATIO` hits).
#[inline]
pub(crate) fn is_disabled(uid: u64, def: DefId) -> bool {
    TABLE.with(|t| {
        let t = t.borrow();
        let Some(&(lookups, hits)) = t.stats.get(&(uid, def)) else {
            return false;
        };
        lookups >= PROBATION && (hits as u64) * (MIN_HIT_RATIO as u64) < lookups as u64
    })
}

/// Probe the memo table with borrowed arguments (zero allocation on hit).
fn lookup(uid: u64, def: DefId, keep_lazy: bool, args: &[&Value]) -> Lookup {
    TABLE.with(|t| {
        let mut t = t.borrow_mut();
        let (lookups, hits) = *t.stats.get(&(uid, def)).unwrap_or(&(0, 0));
        if lookups >= PROBATION && (hits as u64) * (MIN_HIT_RATIO as u64) < lookups as u64 {
            return Lookup::Disabled;
        }
        let q = BorrowedKey { uid, def, keep_lazy, args };
        let v = t.entries.get(&q as &dyn MemoKey).cloned();
        let s = t.stats.entry((uid, def)).or_default();
        s.0 = s.0.saturating_add(1);
        if let Some(v) = v {
            s.1 = s.1.saturating_add(1);
            Lookup::Hit(v)
        } else {
            Lookup::Miss
        }
    })
}

/// Record a computed value for `(uid, def, keep_lazy, args)` if it is small.
fn insert(uid: u64, def: DefId, keep_lazy: bool, args: Vec<Value>, v: &Value) {
    let mut budget = MAX_VALUE_NODES;
    if !small(v, &mut budget) {
        return;
    }
    let key = Key { uid, def, keep_lazy, args };
    TABLE.with(|t| {
        let mut t = t.borrow_mut();
        if t.entries.len() >= MAX_ENTRIES {
            t.entries.clear();
        }
        t.entries.insert(key, v.clone());
    });
}

impl Interp {
    /// Shared constant-context memoized call protocol across the AST and
    /// compiled-`Code` interpreter tiers. Evaluates arguments left to right as
    /// borrowed `Cow`s (stack-allocated for arity `<= 4`, avoiding heap
    /// allocation and `Value` clones on cache hits), defers non-depth argument
    /// errors when `self.def_defer_errors[d]` is set, and probes/populates the
    /// thread-local memo table.
    pub(crate) fn call_def_memo_with<'a>(
        self: &'a Arc<Self>,
        d: DefId,
        cx: &Ctx<'a>,
        span: Span,
        mut eval_arg: impl FnMut(usize) -> EResult<Cow<'a>>,
        bind_arg: impl Fn(usize) -> Binding,
    ) -> EResult<Value> {
        const MEMO_INLINE: usize = 4;
        let params = &self.prog.defs[d.idx()].params;
        let defer_errors = self.def_defer_errors[d.idx()];
        let n = params.len();
        let mut inline: [Option<Cow<'a>>; MEMO_INLINE] = [const { None }; MEMO_INLINE];
        let mut heap: Vec<Cow<'a>> = if n > MEMO_INLINE { Vec::with_capacity(n) } else { Vec::new() };
        let mut deferred: Option<Vec<Binding>> = None;
        for i in 0..n {
            match eval_arg(i) {
                Ok(v) => match &mut deferred {
                    Some(bs) => bs.push(Binding::Val(v.into_owned())),
                    None if n <= MEMO_INLINE => inline[i] = Some(v),
                    None => heap.push(v),
                },
                Err(err) if defer_errors && !crate::depth::is_depth_error(&err) => {
                    let bs = deferred.get_or_insert_with(|| {
                        if n <= MEMO_INLINE {
                            inline[..i].iter_mut().map(|x| Binding::Val(x.take().unwrap().into_owned())).collect()
                        } else {
                            heap.drain(..).map(|x| Binding::Val(x.into_owned())).collect()
                        }
                    });
                    bs.push(bind_arg(i));
                }
                Err(err) => return Err(err),
            }
        }
        if let Some(bs) = deferred {
            let env2 = Env::default().bind_all(params.iter().copied().zip(bs));
            return self.def_body(d, &env2, cx, span);
        }
        let mut inline_refs: [&Value; MEMO_INLINE] = [&Value::Bool(false); MEMO_INLINE];
        let heap_refs: Vec<&Value>;
        let refs: &[&Value] = if n <= MEMO_INLINE {
            for i in 0..n {
                inline_refs[i] = &**inline[i].as_ref().unwrap();
            }
            &inline_refs[..n]
        } else {
            heap_refs = heap.iter().map(|x| &**x).collect();
            &heap_refs
        };
        let res = if keyable_refs(refs) { lookup(self.uid, d, cx.keep_lazy, refs) } else { Lookup::Disabled };
        if let Lookup::Hit(v) = res {
            return Ok(v);
        }
        let owned: Vec<Value> = if n <= MEMO_INLINE {
            inline[..n].iter_mut().map(|x| x.take().unwrap().into_owned()).collect()
        } else {
            heap.into_iter().map(Cow::into_owned).collect()
        };
        if matches!(res, Lookup::Miss) {
            let env2 = Env::default().bind_all(params.iter().copied().zip(owned.iter().cloned().map(Binding::Val)));
            let v = self.def_body(d, &env2, cx, span)?;
            insert(self.uid, d, cx.keep_lazy, owned, &v);
            return Ok(v);
        }
        let env2 = Env::default().bind_all(params.iter().copied().zip(owned.into_iter().map(Binding::Val)));
        self.def_body(d, &env2, cx, span)
    }
}
