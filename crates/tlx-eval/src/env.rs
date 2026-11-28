//! Evaluation environments: persistent linked lists of local bindings.
//! `LocalId`s are unique per binding site, so lookup finds the innermost
//! binding even under recursion.

use std::sync::Arc;

use tlx_sema::hir::{Expr, ExprId, LocalId, OpRef};
use tlx_sema::Program;
use tlx_value::Value;

#[derive(Clone, Default)]
pub struct Env(Option<Arc<Frame<[Slot]>>>);

/// Bindings made together (`Env::bind_all`: a call's parameters, a tuple
/// binder's variables, a LET's caches) in one allocation, the innermost
/// last; a single binding is a frame of one.
struct Frame<S: ?Sized> {
    next: Env,
    slots: S,
}

struct Slot {
    id: LocalId,
    binding: Binding,
}

#[derive(Clone)]
pub enum Binding {
    Val(Value),
    /// Higher-order operator argument.
    Op(OpVal),
    /// Call-by-name argument (used when expanding operators inside actions, so
    /// that `x' = e` is still recognized through operator parameters).
    Thunk(Arc<Thunk>),
    /// Call-by-name argument that is an expression of the program (the
    /// common case of `Thunk`, without reference counting the expression).
    Name(ExprId, Env),
    /// The value of a 0-ary LET definition, computed at most once per
    /// evaluation of the LET (bound under `let_cache_key`).
    LetCache(LetCell),
}

/// The value cache of a 0-ary LET definition (`Binding::LetCache`): a cell
/// of the caches of the definitions of its LET (allocated together).
#[derive(Clone)]
pub enum LetCell {
    /// A cache the environment owns (e.g. holding a value computed
    /// elsewhere): cell 0.
    Owned(Arc<[std::sync::OnceLock<Value>]>),
    /// Cell `i` of caches owned by the evaluation of their LET
    /// (`LetFrame`), which environments only refer to: a lazy value cached
    /// there captures the environment (`{x \in S : P}`, `[x \in S |-> e]`),
    /// which would otherwise keep its own cache, and so itself, alive (an
    /// `Arc` cycle, leaked). Once the evaluation of the LET has ended, the
    /// definition is evaluated again where a lazy value uses it (it is
    /// deterministic).
    Frame(std::sync::Weak<[std::sync::OnceLock<Value>]>, u32),
}

impl LetCell {
    /// A cache holding `v`.
    pub fn with_value(v: Value) -> LetCell {
        LetCell::Owned(Arc::new([std::sync::OnceLock::from(v)]))
    }

    /// The cache, unless the evaluation of its LET has ended.
    pub fn get(&self) -> Option<LetRef> {
        match self {
            LetCell::Owned(c) => Some(LetRef(c.clone(), 0)),
            LetCell::Frame(w, i) => w.upgrade().map(|c| LetRef(c, *i)),
        }
    }
}

/// A LET definition's cache (`LetCell::get`).
pub struct LetRef(Arc<[std::sync::OnceLock<Value>]>, u32);

impl std::ops::Deref for LetRef {
    type Target = std::sync::OnceLock<Value>;

    fn deref(&self) -> &std::sync::OnceLock<Value> {
        &self.0[self.1 as usize]
    }
}

/// The caches of the definitions of a LET (`Interp::let_env`), alive while
/// its body is evaluated.
pub struct LetFrame {
    _cells: Option<Arc<[std::sync::OnceLock<Value>]>>,
}

impl LetFrame {
    pub(crate) fn new(cells: Option<Arc<[std::sync::OnceLock<Value>]>>) -> LetFrame {
        LetFrame { _cells: cells }
    }
}

/// The environment key of the value cache of LET definition `d` (a reserved
/// range of local ids, counted down from the top).
pub fn let_cache_key(d: tlx_sema::hir::DefId) -> LocalId {
    LocalId(u32::MAX - d.0)
}

/// Whether `l` is a `let_cache_key`.
pub fn is_let_cache_key(l: LocalId) -> bool {
    l.0 > u32::MAX / 2
}

/// The environment key under which the compiled tier hands the value of
/// 0-ary state-level definition `d` in the current state (or, `primed`, in
/// the complete next state) to an interpreter fallback: it seeds the
/// context's `DefCache`. Reserved ranges below the LET cache keys.
pub fn def_value_key(d: tlx_sema::hir::DefId, primed: bool) -> LocalId {
    LocalId(if primed { u32::MAX / 4 - d.0 } else { u32::MAX / 2 - d.0 })
}

/// The definition (and whether primed) of a `def_value_key`, if `l` is one.
pub fn def_of_value_key(l: LocalId) -> Option<(tlx_sema::hir::DefId, bool)> {
    use tlx_sema::hir::DefId;
    if is_let_cache_key(l) {
        None
    } else if l.0 > u32::MAX / 4 {
        Some((DefId(u32::MAX / 2 - l.0), false))
    } else if l.0 > u32::MAX / 8 {
        Some((DefId(u32::MAX / 4 - l.0), true))
    } else {
        None
    }
}

impl Binding {
    /// The expression and environment of a call-by-name argument.
    pub fn by_name<'a>(&'a self, prog: &'a Program) -> Option<(&'a Expr, &'a Env)> {
        match self {
            Binding::Thunk(t) => Some((&t.expr, &t.env)),
            Binding::Name(id, env) => Some((prog.arena_expr(*id), env)),
            _ => None,
        }
    }
}

pub struct Thunk {
    pub expr: Expr,
    pub env: Env,
    /// Some: the argument has one value per context (deterministic, not
    /// action-level), so its first unprimed evaluation is kept here (the
    /// compiled tier's interpreter fallbacks; TLC's LazyValue caching).
    pub memo: Option<std::sync::OnceLock<Value>>,
}

#[derive(Clone)]
pub enum OpVal {
    Ref(OpRef),
    Lambda { params: Arc<[LocalId]>, body: Expr, env: Env },
}

impl std::fmt::Debug for Env {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Env(..)")
    }
}

impl Env {
    pub fn bind(&self, id: LocalId, binding: Binding) -> Env {
        self.clone().frame([Slot { id, binding }])
    }

    fn frame<const N: usize>(self, slots: [Slot; N]) -> Env {
        debug_assert!((1..N).all(|i| slots[..i].iter().all(|s| s.id != slots[i].id)), "a frame binds a local twice");
        Env(Some(Arc::new(Frame { next: self, slots })))
    }

    /// `self` extended with `entries`, whose ids are distinct (parameters,
    /// the variables of a binder, the definitions of a LET), in one
    /// allocation per four.
    pub fn bind_all(&self, entries: impl IntoIterator<Item = (LocalId, Binding)>) -> Env {
        let mut out = self.clone();
        let mut it = entries.into_iter().map(|(id, binding)| Slot { id, binding });
        loop {
            let Some(a) = it.next() else { return out };
            let Some(b) = it.next() else { return out.frame([a]) };
            let Some(c) = it.next() else { return out.frame([a, b]) };
            let Some(d) = it.next() else { return out.frame([a, b, c]) };
            out = out.frame([a, b, c, d]);
        }
    }

    /// `self` without its innermost binding of `id` (the bindings above it
    /// are copied, the ones below it shared), or `None` if `id` is not
    /// bound.
    pub(crate) fn without(&self, id: LocalId) -> Option<Env> {
        let mut above = Vec::new();
        let mut cur = &self.0;
        while let Some(f) = cur {
            if let Some(i) = f.slots.iter().rposition(|s| s.id == id) {
                let copy = |s: &Slot| (s.id, s.binding.clone());
                let mut out = f.next.bind_all(f.slots[..i].iter().chain(&f.slots[i + 1..]).map(copy));
                for g in above.into_iter().rev() {
                    let g: &Frame<[Slot]> = g;
                    out = out.bind_all(g.slots.iter().map(copy));
                }
                return Some(out);
            }
            above.push(&**f);
            cur = &f.next.0;
        }
        None
    }

    pub fn bind_val(&self, id: LocalId, v: Value) -> Env {
        self.bind(id, Binding::Val(v))
    }

    /// Bind the innermost local to `v` instead, in place, if nothing else
    /// refers to this environment; otherwise give `v` back.
    pub(crate) fn rebind_head(&mut self, v: Value) -> Result<(), Value> {
        match self.0.as_mut().and_then(Arc::get_mut).and_then(|f| f.slots.last_mut()) {
            Some(slot) => {
                slot.binding = Binding::Val(v);
                Ok(())
            }
            None => Err(v),
        }
    }

    /// `self` extended with all bindings of `other` (oldest first). Safe to
    /// combine environments because local ids are unique per binding site.
    pub fn extend_from(&self, other: &Env) -> Env {
        let mut entries = Vec::new();
        other.for_each_slot(&mut |s| entries.push((s.id, s.binding.clone())));
        let mut out = self.clone();
        for (id, b) in entries.into_iter().rev() {
            if out.lookup(id).is_none() {
                out = out.bind(id, b);
            }
        }
        out
    }

    /// Whether any binding reachable in `self` satisfies `pred`.
    pub(crate) fn any_binding(&self, pred: &mut impl FnMut(&Binding) -> bool) -> bool {
        let mut cur = &self.0;
        while let Some(f) = cur {
            for s in f.slots.iter().rev() {
                if pred(&s.binding) {
                    return true;
                }
            }
            cur = &f.next.0;
        }
        false
    }

    /// Whether `self` and `other` certainly bind the same locals the same
    /// way: the same ids in the same order (and frames), equal values, and
    /// by-name arguments of the same expression node in such environments.
    /// False when unsure (operator arguments, LET caches).
    pub fn same_bindings(&self, other: &Env, prog: &Program) -> bool {
        let (mut a, mut b) = (&self.0, &other.0);
        loop {
            match (a, b) {
                (None, None) => return true,
                (Some(x), Some(y)) => {
                    if std::ptr::addr_eq(Arc::as_ptr(x), Arc::as_ptr(y)) {
                        return true;
                    }
                    let same = x.slots.len() == y.slots.len()
                        && x.slots.iter().zip(y.slots.iter()).all(|(s, t)| {
                            s.id == t.id
                                && match (&s.binding, &t.binding) {
                                    (Binding::Val(v), Binding::Val(w)) => v == w,
                                    (p, q) => match (p.by_name(prog), q.by_name(prog)) {
                                        (Some((e, env)), Some((f, fenv))) => Arc::ptr_eq(&e.kind, &f.kind) && env.same_bindings(fenv, prog),
                                        _ => false,
                                    },
                                }
                        });
                    if !same {
                        return false;
                    }
                    (a, b) = (&x.next.0, &y.next.0);
                }
                _ => return false,
            }
        }
    }

    /// Visits the bindings, innermost first.
    pub fn for_each_binding(&self, f: &mut dyn FnMut(&Binding)) {
        self.for_each_slot(&mut |s| f(&s.binding));
    }

    fn for_each_slot(&self, f: &mut dyn FnMut(&Slot)) {
        let mut cur = &self.0;
        while let Some(n) = cur {
            n.slots.iter().rev().for_each(&mut *f);
            cur = &n.next.0;
        }
    }

    /// The identity of this environment (of its innermost frame).
    pub(crate) fn id(&self) -> usize {
        self.0.as_ref().map_or(0, |n| Arc::as_ptr(n) as *const () as usize)
    }

    pub fn lookup(&self, id: LocalId) -> Option<&Binding> {
        let mut cur = &self.0;
        while let Some(n) = cur {
            // (A single binding, the common case, without a loop; the ids
            // of a frame are distinct.)
            match &n.slots {
                [s] if s.id == id => return Some(&s.binding),
                [_] => {}
                slots => {
                    if let Some(s) = slots.iter().find(|s| s.id == id) {
                        return Some(&s.binding);
                    }
                }
            }
            cur = &n.next.0;
        }
        None
    }
}
