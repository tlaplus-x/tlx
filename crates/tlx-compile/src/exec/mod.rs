//! Closure-compiled IR execution and shared state/memo helpers.

pub mod encops;
pub mod fast;
pub mod memo;
pub mod refops;
mod words;

use std::cell::RefCell;
use std::rc::Rc;
use std::sync::Arc;

use tlx_eval::eval::StateMemo;
use tlx_eval::Interp;
use tlx_value::Value;

pub(crate) mod eval {
    /// Deepest nesting of compiled function calls (deeper, or when the native
    /// stack runs low: the interpreter takes over).
    pub(crate) const MAX_CALL_DEPTH: u32 = 10_000;
    /// Most calls of budgeted functions (recursive function definitions,
    /// which do not cache their points as TLC does) per outermost call (more:
    /// the interpreter takes over).
    pub(crate) const MAX_BUDGETED_CALLS: u64 = 100_000;
}

thread_local! {
    /// Memos of the state-level definitions of recently used encoded
    /// states (most recently used last), keyed by the interpreter, the
    /// layout (held, so that its address is not reused) and the state's
    /// words: [0] of current states, [1] of complete next states (kept
    /// apart so that the successors of a state do not evict its memo).
    static DEF_MEMOS: RefCell<[Vec<DefMemo>; 2]> = const { RefCell::new([Vec::new(), Vec::new()]) };
}

struct DefMemo {
    ip: u64,
    gc_gen: u64,
    layout: Arc<tlx_layout::Layout>,
    words: Box<[u64]>,
    memo: Rc<StateMemo>,
}

/// Number of states in each table of `DEF_MEMOS`.
const DEF_MEMO_STATES: usize = 4;

/// The definition memo of the encoded state `words` of `layout`, shared
/// by the interpreter fallbacks of all the runs (regions, predicates,
/// action properties) on that state as the current state (`next`: as the
/// complete next state of a step), as the interpreter memoizes per state.
pub(crate) fn def_memo(ip: &Interp, layout: &Arc<tlx_layout::Layout>, words: &[u64], next: bool) -> Rc<StateMemo> {
    let gc_gen = memo::store_gc_gen();
    DEF_MEMOS.with(|m| {
        let m = &mut m.borrow_mut()[next as usize];
        let uid = ip.uid();
        if let Some(i) = m.iter().rposition(|e| e.gc_gen == gc_gen && *e.words == *words && e.ip == uid && Arc::ptr_eq(&e.layout, layout)) {
            let memo = m[i].memo.clone();
            if i + 1 != m.len() {
                let e = m.remove(i);
                m.push(e);
            }
            return memo;
        }
        let memo = Rc::new(StateMemo::default());
        if m.len() == DEF_MEMO_STATES {
            // Reuse the least recently used entry.
            let mut e = m.remove(0);
            if e.words.len() == words.len() {
                e.words.copy_from_slice(words);
            } else {
                e.words = words.into();
            }
            if !Arc::ptr_eq(&e.layout, layout) {
                e.layout = layout.clone();
            }
            e.ip = uid;
            e.gc_gen = gc_gen;
            e.memo = memo.clone();
            m.push(e);
        } else {
            m.push(DefMemo { ip: uid, gc_gen, layout: layout.clone(), words: words.into(), memo: memo.clone() });
        }
        memo
    })
}

/// The encoded states of a run, as the source of its definition cache's
/// memos (`def_memo`): `s1` only if it is complete and stays fixed.
pub(crate) struct StateKeys<'a> {
    pub ip: &'a Interp,
    pub layout: &'a Arc<tlx_layout::Layout>,
    pub s0: &'a [u64],
    pub s1: Option<&'a [u64]>,
}

impl tlx_eval::eval::MemoSource for StateKeys<'_> {
    fn memo(&self, next: bool) -> Rc<StateMemo> {
        match (next, self.s1) {
            (false, _) => def_memo(self.ip, self.layout, self.s0, false),
            (true, Some(s1)) => def_memo(self.ip, self.layout, s1, true),
            (true, None) => Rc::default(),
        }
    }
}

/// A borrowed, partially assigned next state (mixed-mode regions in
/// actions and transition predicates, docs/mixed-mode.md §5).
#[derive(Clone, Copy, Debug)]
pub struct S1View<'a> {
    /// The encoded next state (`typing.layout.words` words).
    pub words: &'a [u64],
    /// Per state variable: assigned in `words` (statically known at the
    /// region's call site).
    pub assigned: &'a [bool],
}

/// Decodes the current state's values (at most once per run, and only
/// if a value-level operation needs them). The compiled model passes its
/// per-worker cache (`EncModel`), so a state is decoded once for all its
/// actions and predicates.
pub type S0Decoder<'a> = dyn Fn(&[u64]) -> Arc<[Value]> + 'a;
