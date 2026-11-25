//! In-place evaluation of encoded updates.
//!
//! An `EXCEPT` on an encoded value copies its base and overwrites one
//! slot. Chained updates (`[f EXCEPT ![a].x = 1, ![a].y = 2]` is a `Let`
//! of the first update around the second, and a nested path `![a].x`
//! updates a copy of `f[a]`) copy the whole value at every step. A `Plan`
//! computes such an expression directly into a destination (the next-state
//! slot of an assigned variable, or the expression's own buffer): the base
//! is copied once, every update writes its slot in place (also insertions
//! into sorted-array sets and bitset operations), a `Let` whose value can
//! be computed in place is computed into the destination and its temp
//! names the destination, and a slot that already holds the base's value
//! at that path (`![a].x = v` updates `f[a]`, which the destination holds)
//! is not copied again.
//!
//! The plan is the same for every backend (C, JIT, closure executor); each
//! backend emits it with its own primitives. Plans are only built when
//! they are valid: an expression evaluated after a write to the
//! destination never reads a temp whose words live in the destination and
//! may have been overwritten since the temp was bound (`Planner::check`).
//! Evaluation order changes (a base is copied before the new slot value
//! is computed), which is unobservable: compiled code has no side effects
//! and any runtime error abandons the whole evaluation.

use std::collections::HashMap;

use crate::ir::*;
use crate::types::Typing;

/// How to update one fixed field inside [`Plan::At`]: word-aligned fields run
/// any nested plan, whereas packed sub-word bitfields either keep their
/// existing bits (`None`) or evaluate and insert a scalar expression (`Some`).
#[derive(Debug)]
pub enum AtUpdate<'e> {
    Word { offset: usize, value: Box<Plan<'e>> },
    Bits { pos: BitPos, value: Option<&'e Expr> },
}

/// How to update one dynamically indexed slot inside [`Plan::AtIndex`]:
/// word-aligned slots run any nested plan, whereas packed sub-word slots either
/// keep their existing bits (`None`) or evaluate and insert a scalar (`Some`).
#[derive(Debug)]
pub enum IndexUpdate<'e> {
    Words { elem_words: usize, value: Box<Plan<'e>> },
    Bits { bits: u8, value: Option<&'e Expr> },
}

/// How to compute an encoded expression into a destination of its size.
#[derive(Debug)]
pub enum Plan<'e> {
    /// The destination already holds the value.
    Keep,
    /// Evaluate the expression and copy it into the destination (the value
    /// may overlap the destination: a move).
    Copy(&'e Expr),
    /// Bind `temp` to the value of `value` (an ordinary `Let`), then `body`.
    Let { temp: Temp, value: &'e Expr, body: Box<Plan<'e>> },
    /// Compute `value` into the destination, bind `temp` to the
    /// destination (same encoding), then `body`.
    LetHere { temp: Temp, value: Box<Plan<'e>>, body: Box<Plan<'e>> },
    /// `base` into the destination, then apply `update` to one fixed field.
    At { base: Box<Plan<'e>>, update: AtUpdate<'e> },
    /// `base` into the destination, then evaluate `arg` and, if it selects a
    /// slot (else nothing more), apply `update` to that slot.
    AtIndex { base: Box<Plan<'e>>, arg: &'e Expr, map: &'e IndexMap, update: IndexUpdate<'e> },
    /// Either plan, by a boolean condition.
    If { cond: &'e Expr, then: Box<Plan<'e>>, els: Box<Plan<'e>> },
    /// Parts at consecutive word offsets.
    Concat(Vec<(usize, Plan<'e>)>),
    /// `set` (a sorted-array set) into the destination, then insert `elem`
    /// in place (more than `max_card` elements: runtime error).
    Insert { set: Box<Plan<'e>>, elem: &'e Expr, elem_words: u32, max_card: u32 },
    /// `a` (a bitset) into the destination, then combine it word by word
    /// with `b` in place.
    Bits { op: SetOp, a: Box<Plan<'e>>, b: &'e Expr },
}

impl Plan<'_> {
    /// Whether the plan is just a copy of the whole value (no gain over
    /// evaluating the expression).
    pub fn is_copy(&self) -> bool {
        matches!(self, Plan::Copy(_))
    }
}

/// Whether `e` builds an encoded value by updating another one, so that
/// computing it in place saves copies (`plan` gains over evaluating it).
pub fn is_update(e: &Expr) -> bool {
    match &*e.kind {
        ExprKind::ExceptAt { .. } | ExprKind::ExceptIndex { .. } => matches!(e.ty, Ty::Enc(_)),
        // (A single insertion copies the set while inserting.)
        ExprKind::SortedInsert { set, .. } => is_update(set) || matches!(&*set.kind, ExprKind::SortedInsert { .. }),
        ExprKind::BitSetOp(_, a, _) => is_update(a),
        ExprKind::Let { body, .. } => is_update(body),
        _ => false,
    }
}

/// The plan computing the encoded expression `e` into a destination whose
/// current contents are unknown (at worst `Plan::Copy(e)`).
pub fn plan<'e>(e: &'e Expr, t: &Typing) -> Plan<'e> {
    plan_with(e, &|sid| t.words(sid))
}

/// `plan` with the encoding sizes given by `words`.
fn plan_with<'e>(e: &'e Expr, words: &dyn Fn(ShapeId) -> u32) -> Plan<'e> {
    let mut p = Planner { words, pure: HashMap::new(), st: State::default() };
    p.plan(e, None).unwrap_or(Plan::Copy(e))
}

/// A word path from a root value (what a destination holds).
#[derive(Clone, Debug)]
struct Path<'e> {
    root: Root,
    steps: Vec<Step<'e>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Root {
    Temp(Temp),
    Var(u32),
    Next(u32),
}

#[derive(Clone, Debug)]
enum Step<'e> {
    Off(usize),
    Bits(BitPos),
    Idx(&'e Expr, &'e IndexMap, SlotLayout),
}

impl<'e> Path<'e> {
    fn push(mut self, s: Step<'e>) -> Path<'e> {
        match (self.steps.last_mut(), &s) {
            (Some(Step::Off(a)), Step::Off(b)) => *a = a.saturating_add(*b),
            (Some(last @ Step::Off(_)), Step::Bits(p)) => {
                let Step::Off(a) = *last else { unreachable!() };
                *last = Step::Bits(p.offset_words(a));
            }
            (_, Step::Off(0)) => {}
            _ => self.steps.push(s),
        }
        self
    }

    fn push_loc(self, loc: FieldLoc) -> Path<'e> {
        match loc {
            FieldLoc::Words(w) => self.push(Step::Off(w)),
            FieldLoc::Bits(p) => self.push(Step::Bits(p)),
        }
    }
}

#[derive(Clone, Default)]
struct State {
    /// Temps whose words are (possibly) in the destination, with the
    /// number of writes to the destination when they were bound.
    tainted: HashMap<Temp, u32>,
    /// Writes to the destination so far.
    writes: u32,
}

struct Planner<'e, 't> {
    words: &'t dyn Fn(ShapeId) -> u32,
    /// `Let` temps bound to pointer expressions (a temp is the same value
    /// as its definition).
    pure: HashMap<Temp, &'e Expr>,
    st: State,
}

impl<'e> Planner<'e, '_> {
    /// Whether `e` already equals the value stored at `holds`.
    fn is_kept(&self, e: &'e Expr, holds: Option<&Path<'e>>) -> bool {
        matches!((holds, self.path_of(e)), (Some(h), Some(p)) if self.same_path(h, &p))
    }

    /// Plan a packed bitfield scalar value: `None` when the destination already
    /// holds it, else `Some(e)` after checking aliasing and counting the write.
    fn plan_bits(&mut self, e: &'e Expr, holds: Option<&Path<'e>>) -> Option<Option<&'e Expr>> {
        if self.is_kept(e, holds) {
            return Some(None);
        }
        self.check(e)?;
        self.st.writes += 1;
        Some(Some(e))
    }

    /// Plan `e` into a destination holding `holds` (None: unknown); None if
    /// no valid plan exists from the current state (the caller falls back).
    fn plan(&mut self, e: &'e Expr, holds: Option<&Path<'e>>) -> Option<Plan<'e>> {
        if self.is_kept(e, holds) {
            return Some(Plan::Keep);
        }
        let saved = self.st.clone();
        if let Some(p) = self.node(e, holds) {
            return Some(p);
        }
        self.st = saved;
        self.copy(e)
    }

    fn copy(&mut self, e: &'e Expr) -> Option<Plan<'e>> {
        self.check(e)?;
        self.st.writes += 1;
        Some(Plan::Copy(e))
    }

    fn node(&mut self, e: &'e Expr, holds: Option<&Path<'e>>) -> Option<Plan<'e>> {
        match &*e.kind {
            ExprKind::Let { temp, value, body } => {
                if value.ty == e.ty {
                    let saved = self.st.clone();
                    if let Some(v) = self.plan(value, holds) {
                        // (A value the destination already holds is bound
                        // where it is: the temp does not depend on the
                        // destination.)
                        if !matches!(v, Plan::Copy(_) | Plan::Keep) {
                            self.st.tainted.insert(*temp, self.st.writes);
                            let here = Path { root: Root::Temp(*temp), steps: Vec::new() };
                            let b = self.plan(body, Some(&here))?;
                            return Some(Plan::LetHere { temp: *temp, value: Box::new(v), body: Box::new(b) });
                        }
                    }
                    self.st = saved;
                }
                self.check(value)?;
                if self.mentions_tainted(value) {
                    self.st.tainted.insert(*temp, self.st.writes);
                }
                if self.path_of(value).is_some() {
                    self.pure.insert(*temp, value);
                }
                let b = self.plan(body, holds)?;
                Some(Plan::Let { temp: *temp, value, body: Box::new(b) })
            }
            ExprKind::ExceptAt { base, loc, value } => {
                if !matches!(e.ty, Ty::Enc(_)) || !matches!(value.ty, Ty::Enc(_)) {
                    return None;
                }
                let (b, inner) = self.base(base, holds)?;
                let inner = inner.map(|p| p.push_loc(*loc));
                let update = match *loc {
                    FieldLoc::Words(offset) => AtUpdate::Word { offset, value: Box::new(self.plan(value, inner.as_ref())?) },
                    FieldLoc::Bits(pos) => AtUpdate::Bits { pos, value: self.plan_bits(value, inner.as_ref())? },
                };
                Some(Plan::At { base: Box::new(b), update })
            }
            ExprKind::ExceptIndex { base, arg, map, slot, value } => {
                if !matches!(e.ty, Ty::Enc(_)) || !matches!(value.ty, Ty::Enc(_)) {
                    return None;
                }
                let (b, inner) = self.base(base, holds)?;
                self.check(arg)?;
                let inner = inner.map(|p| p.push(Step::Idx(arg, map, *slot)));
                // The value is computed only if the slot exists.
                let before = self.st.clone();
                let update = match *slot {
                    SlotLayout::Words(elem_words) => IndexUpdate::Words { elem_words, value: Box::new(self.plan(value, inner.as_ref())?) },
                    SlotLayout::Bits(bits) => IndexUpdate::Bits { bits, value: self.plan_bits(value, inner.as_ref())? },
                };
                self.join(&before);
                Some(Plan::AtIndex { base: Box::new(b), arg, map, update })
            }
            ExprKind::If(c, t, f) => {
                if t.ty != e.ty || f.ty != e.ty {
                    return None;
                }
                self.check(c)?;
                let before = self.st.clone();
                let then = self.plan(t, holds)?;
                let after_then = std::mem::replace(&mut self.st, before);
                let els = self.plan(f, holds)?;
                self.join(&after_then);
                Some(Plan::If { cond: c, then: Box::new(then), els: Box::new(els) })
            }
            ExprKind::Concat(xs) => {
                let mut parts = Vec::with_capacity(xs.len());
                let mut off = 0usize;
                for x in xs {
                    let Ty::Enc(sid) = x.ty else { return None };
                    let w = (self.words)(sid) as usize;
                    let h = holds.map(|h| h.clone().push(Step::Off(off)));
                    parts.push((off, self.plan(x, h.as_ref())?));
                    off += w;
                }
                Some(Plan::Concat(parts))
            }
            ExprKind::SortedInsert { set, elem, elem_words, max_card } => {
                let s = self.plan(set, holds)?;
                // The insertion moves words of the destination: the
                // element must not be among them.
                if self.mentions_tainted(elem) {
                    return None;
                }
                self.st.writes += 1;
                Some(Plan::Insert { set: Box::new(s), elem, elem_words: *elem_words, max_card: *max_card })
            }
            ExprKind::BitSetOp(op, a, b) => {
                let x = self.plan(a, holds)?;
                self.check(b)?;
                self.st.writes += 1;
                Some(Plan::Bits { op: *op, a: Box::new(x), b })
            }
            _ => None,
        }
    }

    /// Plan the base of an update; returns what the destination holds
    /// afterwards (if it is a path).
    fn base(&mut self, base: &'e Expr, holds: Option<&Path<'e>>) -> Option<(Plan<'e>, Option<Path<'e>>)> {
        let b = self.plan(base, holds)?;
        let now = match (&b, self.path_of(base)) {
            (_, Some(p)) => Some(p),
            (Plan::Keep, None) => holds.cloned(),
            _ => None,
        };
        Some((b, now))
    }

    /// After one of two alternative paths (the other one being `other`'s
    /// state): a temp bound before both is stale if either wrote.
    fn join(&mut self, other: &State) {
        self.st.writes = self.st.writes.max(other.writes) + (self.st.writes != other.writes) as u32;
        for (t, w) in &other.tainted {
            self.st.tainted.entry(*t).or_insert(*w);
        }
    }

    /// Whether `e` may be evaluated now: every temp it reads that lives in
    /// the destination was bound after the last write to it.
    fn check(&self, e: &Expr) -> Option<()> {
        if self.st.tainted.is_empty() {
            return Some(());
        }
        let mut ok = true;
        visit_temps(e, &mut |t| {
            if self.st.tainted.get(&t).is_some_and(|w| *w != self.st.writes) {
                ok = false;
            }
        });
        ok.then_some(())
    }

    fn mentions_tainted(&self, e: &Expr) -> bool {
        let mut any = false;
        visit_temps(e, &mut |t| any |= self.st.tainted.contains_key(&t));
        any
    }

    /// `e` as a word path from a root value, if it is one.
    fn path_of(&self, e: &'e Expr) -> Option<Path<'e>> {
        match &*e.kind {
            ExprKind::Temp(t) => match self.pure.get(t) {
                Some(d) => self.path_of(d),
                None => Some(Path { root: Root::Temp(*t), steps: Vec::new() }),
            },
            ExprKind::Var(v) => Some(Path { root: Root::Var(*v), steps: Vec::new() }),
            ExprKind::NextVar(v) => Some(Path { root: Root::Next(*v), steps: Vec::new() }),
            ExprKind::Slice { base, loc } => Some(self.path_of(base)?.push_loc(*loc)),
            ExprKind::Index { base, arg, map, slot } => Some(self.path_of(base)?.push(Step::Idx(arg, map, *slot))),
            _ => None,
        }
    }

    fn same_path(&self, a: &Path<'e>, b: &Path<'e>) -> bool {
        a.root == b.root
            && a.steps.len() == b.steps.len()
            && a.steps.iter().zip(&b.steps).all(|(x, y)| match (x, y) {
                (Step::Off(i), Step::Off(j)) => i == j,
                (Step::Bits(i), Step::Bits(j)) => i == j,
                (Step::Idx(a1, m1, w1), Step::Idx(a2, m2, w2)) => w1 == w2 && m1 == m2 && self.same(a1, a2),
                _ => false,
            })
    }

    /// Whether two side-effect-free expressions certainly have the same
    /// value (structurally).
    fn same(&self, a: &'e Expr, b: &'e Expr) -> bool {
        if a.ty != b.ty {
            return false;
        }
        if let (Some(p), Some(q)) = (self.path_of(a), self.path_of(b)) {
            return self.same_path(&p, &q);
        }
        match (&*a.kind, &*b.kind) {
            (ExprKind::Const(x), ExprKind::Const(y)) => x == y,
            (ExprKind::ConstWords(x), ExprKind::ConstWords(y)) => x == y,
            (ExprKind::Convert(x), ExprKind::Convert(y)) | (ExprKind::Rank(x), ExprKind::Rank(y)) => self.same(x, y),
            (ExprKind::UnionField { base: x, locs: o1 }, ExprKind::UnionField { base: y, locs: o2 }) => o1 == o2 && self.same(x, y),
            (ExprKind::UnionFieldInt { base: x, entries: e1 }, ExprKind::UnionFieldInt { base: y, entries: e2 }) => {
                e1 == e2 && self.same(x, y)
            }
            (ExprKind::IntBin(o1, x1, y1), ExprKind::IntBin(o2, x2, y2)) => o1 == o2 && self.same(x1, x2) && self.same(y1, y2),
            _ => false,
        }
    }
}

/// Call `f` on every temp `e` reads (including those bound inside it).
fn visit_temps(e: &Expr, f: &mut dyn FnMut(Temp)) {
    if let ExprKind::Temp(t) = &*e.kind {
        f(*t);
    }
    e.for_each_child(&mut |c| visit_temps(c, f));
}

#[cfg(test)]
mod tests {
    use super::*;

    // Shapes: 0 = three words, 1 = one word, 2 = two words.
    fn words(sid: ShapeId) -> u32 {
        [3, 1, 2][sid as usize]
    }

    fn var(i: u32) -> Expr {
        Expr::new(Ty::Enc(0), ExprKind::Var(i))
    }

    fn temp(t: Temp, sid: ShapeId) -> Expr {
        Expr::new(Ty::Enc(sid), ExprKind::Temp(t))
    }

    fn word(c: u64) -> Expr {
        Expr::new(Ty::Enc(1), ExprKind::ConstWords(vec![c].into()))
    }

    fn at(base: Expr, offset: usize, value: Expr) -> Expr {
        Expr::new(base.ty, ExprKind::ExceptAt { base, loc: FieldLoc::Words(offset), value })
    }

    fn slice(base: Expr, offset: usize, sid: ShapeId) -> Expr {
        Expr::new(Ty::Enc(sid), ExprKind::Slice { base, loc: FieldLoc::Words(offset) })
    }

    fn let_(temp: Temp, value: Expr, body: Expr) -> Expr {
        Expr::new(body.ty, ExprKind::Let { temp, value, body })
    }

    #[test]
    fn chained_updates_copy_the_base_once() {
        // [x EXCEPT ![1] = a, ![2] = b]
        let e = let_(0, at(var(0), 0, word(7)), at(temp(0, 0), 1, word(8)));
        let p = plan_with(&e, &words);
        let Plan::LetHere { value, body, .. } = &p else { panic!("{p:?}") };
        assert!(
            matches!(
                &**value,
                Plan::At { base, update: AtUpdate::Word { offset: 0, value } }
                    if matches!(**base, Plan::Copy(_)) && matches!(**value, Plan::Copy(_))
            ),
            "{p:?}"
        );
        assert!(matches!(&**body, Plan::At { base, update: AtUpdate::Word { offset: 1, .. } } if matches!(**base, Plan::Keep)), "{p:?}");
    }

    #[test]
    fn nested_path_updates_its_slot_in_place() {
        // [x EXCEPT !.f.g = a] with x.f two words at offset 1.
        let inner = at(slice(var(0), 1, 2), 1, word(7));
        let e = Expr::new(Ty::Enc(0), ExprKind::ExceptAt { base: var(0), loc: FieldLoc::Words(1), value: inner });
        let p = plan_with(&e, &words);
        let Plan::At { base, update: AtUpdate::Word { offset: 1, value } } = &p else { panic!("{p:?}") };
        assert!(matches!(**base, Plan::Copy(_)));
        assert!(
            matches!(
                &**value,
                Plan::At { base, update: AtUpdate::Word { offset: 1, value } }
                    if matches!(**base, Plan::Keep) && matches!(**value, Plan::Copy(_))
            ),
            "{p:?}"
        );
    }

    #[test]
    fn chained_bitfield_updates_share_word_in_place() {
        let pos_a = BitPos::new(0, 63, 1);
        let pos_b = BitPos::new(0, 60, 3);
        let e1 = Expr::new(Ty::Enc(0), ExprKind::ExceptAt { base: var(0), loc: FieldLoc::Bits(pos_a), value: word(1) });
        let e2 = Expr::new(Ty::Enc(0), ExprKind::ExceptAt { base: temp(0, 0), loc: FieldLoc::Bits(pos_b), value: word(5) });
        let e = let_(0, e1, e2);
        let p = plan_with(&e, &words);
        let Plan::LetHere { value, body, .. } = &p else { panic!("{p:?}") };
        assert!(matches!(
            &**value,
            Plan::At { base, update: AtUpdate::Bits { pos, value: Some(_) } } if *pos == pos_a && matches!(**base, Plan::Copy(_))
        ));
        assert!(matches!(
            &**body,
            Plan::At { base, update: AtUpdate::Bits { pos, value: Some(_) } } if *pos == pos_b && matches!(**base, Plan::Keep)
        ));
    }

    #[test]
    fn identity_bitfield_updates_are_kept_without_writing() {
        let pos_a = BitPos::new(0, 63, 1);
        let same_a = Expr::new(Ty::Enc(1), ExprKind::Slice { base: var(0), loc: FieldLoc::Bits(pos_a) });
        let e = Expr::new(Ty::Enc(0), ExprKind::ExceptAt { base: var(0), loc: FieldLoc::Bits(pos_a), value: same_a });
        let p = plan_with(&e, &words);
        assert!(
            matches!(&p, Plan::At { base, update: AtUpdate::Bits { pos, value: None } } if *pos == pos_a && matches!(**base, Plan::Copy(_))),
            "{p:?}"
        );
    }

    #[test]
    fn stale_read_of_the_destination_is_not_planned() {
        // t0 lives in the destination; after slot 1 is written, slot 1 of
        // t0 (its old value) must not be read from there.
        let body = at(at(temp(0, 0), 1, word(8)), 2, slice(temp(0, 0), 1, 1));
        let e = let_(0, at(var(0), 0, word(7)), body);
        let p = plan_with(&e, &words);
        let Plan::LetHere { body, .. } = &p else { panic!("{p:?}") };
        assert!(matches!(**body, Plan::Copy(_)), "{p:?}");
    }

    #[test]
    fn element_in_the_destination_is_not_inserted_in_place() {
        let ins = |s: Expr, x: Expr| Expr::new(Ty::Enc(0), ExprKind::SortedInsert { set: s, elem: x, elem_words: 1, max_card: 2 });
        // LET t0 == x \cup {7} IN t0 \cup {t0[1]}
        let e = let_(0, ins(var(0), word(7)), ins(temp(0, 0), slice(temp(0, 0), 1, 1)));
        let p = plan_with(&e, &words);
        let Plan::LetHere { body, .. } = &p else { panic!("{p:?}") };
        assert!(matches!(**body, Plan::Copy(_)), "{p:?}");
    }
}
