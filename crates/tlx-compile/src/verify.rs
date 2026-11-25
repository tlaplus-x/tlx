//! Compile-time contracts of the typed IR, shared by every backend.
//!
//! This checks representation and memory-layout contracts, not TLA+ validity:
//! a runtime type error or a speculative layout miss remains a runtime event.

use tlx_layout::{
    layout::{bitset_universe, words},
    Shape,
};
use tlx_value::Value;

use crate::ir::*;
use crate::types::Typing;

type Result<T = ()> = std::result::Result<T, String>;

fn require(ok: bool, message: &str) -> Result {
    if ok {
        Ok(())
    } else {
        Err(message.into())
    }
}
fn same(actual: Ty, expected: Ty) -> Result {
    if actual == expected {
        Ok(())
    } else {
        Err(format!("type mismatch: expected {expected:?}, got {actual:?}"))
    }
}

/// The function's available state buffers. Enabled expressions have their own
/// partially assigned next state and may emit without assigning every variable.
#[derive(Clone, Copy)]
pub enum Context {
    Init,
    Action,
    State,
    Transition,
    Value,
}

use crate::lower::summary::{Functions, StateContract, Summary};

fn contracts(t: &Typing) -> Vec<StateContract> {
    let nvars = t.var_sid.len();
    Functions::new(&t.funcs, nvars, |_| Summary::empty(0), |_| None).contracts()
}

struct Check<'a> {
    t: &'a Typing,
    contracts: &'a [StateContract],
    /// `Verified::widths`.
    widths: &'a [bool],
    temps: &'a [Ty],
    defined: Vec<bool>,
    assigned: Vec<bool>,
    current: bool,
    partial: bool,
    repeats: Vec<u32>,
}

impl<'a> Check<'a> {
    fn new(t: &'a Typing, (contracts, widths): (&'a [StateContract], &'a [bool]), temps: &'a [Ty], context: Context) -> Result<Self> {
        let c = Self {
            t,
            contracts,
            widths,
            temps,
            defined: vec![false; temps.len()],
            assigned: vec![matches!(context, Context::Transition); t.var_sid.len()],
            current: !matches!(context, Context::Init),
            partial: matches!(context, Context::Value),
            repeats: Vec::new(),
        };
        for &ty in temps {
            c.ty(ty)?;
            if matches!(ty, Ty::Enc(_)) {
                c.width(ty)?;
            }
        }
        Ok(c)
    }
    fn ty(&self, ty: Ty) -> Result {
        if let Ty::Enc(s) = ty {
            require((s as usize) < self.t.num_shapes(), "unknown shape")?;
        }
        Ok(())
    }
    fn shape(&self, ty: Ty) -> Result<&'a Shape> {
        self.ty(ty)?;
        match ty {
            Ty::Enc(s) => Ok(self.t.shape(s)),
            _ => Err("expected encoded type".into()),
        }
    }
    fn width(&self, ty: Ty) -> Result<usize> {
        self.shape(ty)?;
        let Ty::Enc(s) = ty else { unreachable!() };
        require(self.widths.get(s as usize) == Some(&true), "shape encoding width exceeds IR width")?;
        Ok(self.t.words(s) as usize)
    }
    fn temp(&self, temp: Temp) -> Result<Ty> {
        self.temps.get(temp as usize).copied().ok_or_else(|| "unknown temporary".into())
    }
    fn bind<T>(&mut self, temp: Temp, ty: Ty, body: impl FnOnce(&mut Self) -> Result<T>) -> Result<T> {
        same(self.temp(temp)?, ty)?;
        require(!self.defined[temp as usize], "temporary redefined in its scope")?;
        self.defined[temp as usize] = true;
        let result = body(self);
        self.defined[temp as usize] = false;
        result
    }
    fn source(&mut self, e: &Expr) -> Result<Ty> {
        self.ty(e.ty)?;
        match &*e.kind {
            ExprKind::IntRange(a, b) => {
                self.expect(a, Ty::Int)?;
                self.expect(b, Ty::Int)?;
                Ok(Ty::Int)
            }
            ExprKind::ConstElems { elem, words: data, count } => {
                let w = self.width(Ty::Enc(*elem))?;
                require(w.checked_mul(*count as usize) == Some(data.len()), "constant iteration width/count mismatch")?;
                Ok(Ty::Enc(*elem))
            }
            ExprKind::Subsets(x) => {
                self.expr(x)?;
                self.bitset(x.ty)?;
                Ok(x.ty)
            }
            ExprKind::RefElems(x) => {
                let h = self.handle_ty()?;
                self.expect(x, h)?;
                Ok(h)
            }
            // An encoded set iterated in TLC order: the plan's root node is
            // [opcode, element words, node length, child count, children...], optionally
            // followed by one rank key per element of a bitset universe.
            ExprKind::OrderedSet { set, plan } => {
                self.expr(set)?;
                require(matches!(set.ty, Ty::Enc(_)), "ordered iteration over a boxed set")?;
                let Shape::Set { elem, .. } = self.shape(set.ty)? else {
                    return Err("ordered iteration source is not a set".into());
                };
                let ty = self.shape_ty(elem)?;
                let width = self.width(ty)?;
                let plan = crate::encoded_order::CheckedPlan::new(plan, elem)?;
                require(plan.width() == width, "ordered iteration plan width mismatch")?;
                Ok(ty)
            }
            _ => {
                self.expr(e)?;
                if e.ty == Ty::Val {
                    return Ok(Ty::Val);
                }
                let Shape::Set { elem, .. } = self.shape(e.ty)? else {
                    return Err("iteration source is not a set".into());
                };
                self.shape_ty(elem)
            }
        }
    }
    /// The type of value store handles (the run's `Ref` shape).
    fn handle_ty(&self) -> Result<Ty> {
        self.t.ref_sid().map(Ty::Enc).ok_or_else(|| "value store operation without a store shape".into())
    }
    /// A value store operation: its arguments and result in the
    /// representations `RefOp` states.
    fn ref_op(&mut self, e: &Expr, op: &crate::ir::RefOp, args: &[Expr]) -> Result {
        use crate::ir::RefOp as O;
        let h = self.handle_ty()?;
        let (params, ret): (Vec<Ty>, Ty) = match op {
            O::Domain | O::Head | O::Tail | O::Field(_) => (vec![h], h),
            O::Apply | O::Single | O::Merge | O::Append => (vec![h, h], h),
            O::Select => (vec![h, h], Ty::Int),
            O::ValueAt => (vec![h, Ty::Int], h),
            O::SetAt => (vec![h, Ty::Int, h], h),
            O::Member | O::InDomain | O::Eq => (vec![h, h], Ty::Bool),
            O::Cardinality | O::Len | O::ToInt => (vec![h], Ty::Int),
            O::ToBool => (vec![h], Ty::Bool),
            O::Tuple => (vec![h; args.len()], h),
            O::Record(names) => {
                require(!names.is_empty() && names.len() == args.len(), "record arity mismatch")?;
                (vec![h; args.len()], h)
            }
            O::FromInt => (vec![Ty::Int], h),
            O::FromBool => (vec![Ty::Bool], h),
            O::FromEnc(sid) => {
                require(Ty::Enc(*sid) != h, "value store conversion of a handle")?;
                (vec![Ty::Enc(*sid)], h)
            }
            O::ToEnc(sid) => {
                require(Ty::Enc(*sid) != h, "value store conversion to a handle")?;
                (vec![h], Ty::Enc(*sid))
            }
        };
        same(e.ty, ret)?;
        require(params.len() == args.len(), "value store operation arity mismatch")?;
        for (a, p) in args.iter().zip(params) {
            self.expect(a, p)?;
        }
        Ok(())
    }
    fn shape_ty(&self, s: &Shape) -> Result<Ty> {
        self.t.lookup(s).map(Ty::Enc).ok_or_else(|| "unregistered element shape".into())
    }
    fn expect(&mut self, e: &Expr, ty: Ty) -> Result {
        self.expr(e)?;
        same(e.ty, ty)
    }
    fn bitset(&self, ty: Ty) -> Result<&'a Shape> {
        match self.shape(ty)? {
            Shape::Set { elem, .. } if bitset_universe(elem).is_some() => Ok(elem),
            _ => Err("expected bitset shape".into()),
        }
    }
    fn sequence(&self, ty: Ty, slot: SlotLayout) -> Result<(&'a Shape, usize)> {
        match self.shape(ty)? {
            Shape::Seq { elem, max_len } => {
                require(SlotLayout::of(elem) == slot, "sequence element width mismatch")?;
                Ok((elem, *max_len))
            }
            _ => Err("expected sequence shape".into()),
        }
    }
    fn sorted(&self, ty: Ty, width: u32) -> Result<(&'a Shape, usize)> {
        match self.shape(ty)? {
            Shape::Set { elem, max_card } if bitset_universe(elem).is_none() => {
                require(words(elem) == width as usize, "sorted set element width mismatch")?;
                Ok((elem, *max_card))
            }
            _ => Err("expected sorted set shape".into()),
        }
    }
    fn span(&self, base: Ty, loc: FieldLoc, value: Ty) -> Result {
        let base_width = self.width(base)?;
        let val_width = self.width(value)?;
        match loc {
            FieldLoc::Words(offset) => {
                require(offset.checked_add(val_width).is_some_and(|end| end <= base_width), "encoding slice outside base")
            }
            FieldLoc::Bits(pos) => {
                require(val_width == 1 && self.shape(value)?.is_scalar(), "bitfield slice value width mismatch")?;
                require(pos.valid_in(base_width), "encoding slice outside base")
            }
        }
    }
    fn index(&mut self, base: &Expr, arg: &Expr, map: &IndexMap, slot: SlotLayout, value: Ty) -> Result {
        self.expr(base)?;
        self.expr(arg)?;
        let val_shape = self.shape(value)?;
        let val_width = self.width(value)?;
        require(SlotLayout::of(val_shape) == slot, "index element width mismatch")?;
        match slot {
            SlotLayout::Words(w) => require(val_width == w, "index element width mismatch")?,
            SlotLayout::Bits(_) => require(val_width == 1 && val_shape.is_scalar(), "index element width mismatch")?,
        }
        let slots: Vec<&Shape> = match self.shape(base.ty)? {
            Shape::Tuple(parts) => parts.iter().collect(),
            Shape::Record(fields) => fields.iter().map(|(_, s)| s).collect(),
            Shape::Fcn { dom, range } => vec![range; dom.len()],
            _ => return Err("indexed base has no fixed slots".into()),
        };
        require(slots.iter().all(|s| **s == *val_shape), "index slot shape mismatch")?;
        match map {
            IndexMap::IntRange { lo, n } => {
                same(arg.ty, Ty::Int)?;
                require(*n as usize <= slots.len(), "index span outside base")?;
                require(lo.checked_add(i64::from(*n)).is_some(), "index range overflow")
            }
            IndexMap::Table(table) => {
                require(self.shape(arg.ty)?.is_scalar(), "index table argument is not scalar")?;
                require(table.iter().all(|&i| i == -1 || (i >= 0 && (i as usize) < slots.len())), "index table slot outside base")
            }
        }
    }
    fn expr(&mut self, e: &Expr) -> Result {
        use ExprKind::*;
        self.ty(e.ty)?;
        if matches!(e.ty, Ty::Enc(_)) {
            self.width(e.ty)?;
        }
        match &*e.kind {
            Const(v) => match e.ty {
                Ty::Bool => require(matches!(v, Value::Bool(_)), "boolean constant type mismatch"),
                Ty::Int => require(matches!(v, Value::Int(_)), "integer constant type mismatch"),
                // An unencodable constant is a layout miss, not malformed IR.
                Ty::Val | Ty::Enc(_) => Ok(()),
            },
            ConstWords(w) => require(w.len() == self.width(e.ty)?, "constant encoding width mismatch"),
            Var(v) | NextVar(v) => {
                let ty = self.t.var_sid.get(*v as usize).copied().map(Ty::Enc).ok_or("unknown state variable")?;
                if e.ty != Ty::Val {
                    same(e.ty, ty)?;
                }
                if matches!(&*e.kind, NextVar(_)) {
                    require(self.assigned[*v as usize], "next variable read before assignment")
                } else {
                    require(self.current, "current state read in Init")
                }
            }
            Temp(t) => {
                same(e.ty, self.temp(*t)?)?;
                require(self.defined[*t as usize], "temporary used outside its definition scope")
            }
            Not(x) => {
                same(e.ty, Ty::Bool)?;
                self.expect(x, Ty::Bool)
            }
            And(xs) | Or(xs) => {
                same(e.ty, Ty::Bool)?;
                for x in xs {
                    self.expect(x, Ty::Bool)?;
                }
                Ok(())
            }
            If(c, a, b) => {
                self.expect(c, Ty::Bool)?;
                self.expect(a, e.ty)?;
                self.expect(b, e.ty)
            }
            IntBin(_, a, b) | IntCmp(_, a, b) => {
                same(e.ty, if matches!(&*e.kind, IntBin(..)) { Ty::Int } else { Ty::Bool })?;
                self.expect(a, Ty::Int)?;
                self.expect(b, Ty::Int)
            }
            Neg(x) => {
                same(e.ty, Ty::Int)?;
                self.expect(x, Ty::Int)
            }
            Eq(a, b) => {
                same(e.ty, Ty::Bool)?;
                self.expr(a)?;
                self.expect(b, a.ty)
            }
            Convert(x) => self.expr(x), // Runtime conversions may fail for any valid representation.
            Let { temp, value, body } => {
                self.expr(value)?;
                self.bind(*temp, value.ty, |c| c.expect(body, e.ty))
            }
            Exists { bind, set, body } | Forall { bind, set, body } | Choose { bind, set, body } => {
                let ty = self.source(set)?;
                same(e.ty, if matches!(&*e.kind, Choose { .. }) { ty } else { Ty::Bool })?;
                self.bind(*bind, ty, |c| c.expect(body, Ty::Bool))
            }
            Fold { bind, set, body, .. } => {
                same(e.ty, Ty::Int)?;
                let ty = self.source(set)?;
                self.bind(*bind, ty, |c| c.expect(body, Ty::Int))
            }
            UnionFold { bind, set, body } => {
                // The fold is the word-wise or of the members' encodings: it is
                // the union of the members only where a set is a bitset of one
                // element universe (a larger universe is a sorted array).
                match self.shape(e.ty)? {
                    Shape::Set { elem, .. } if bitset_universe(elem).is_some() => {}
                    _ => return Err("UnionFold over a non-bitset set".into()),
                }
                let ty = self.source(set)?;
                self.bind(*bind, ty, |c| c.expect(body, e.ty))
            }
            Filter { bind, set, pred } => {
                same(e.ty, set.ty)?;
                let ty = self.source(set)?;
                self.bind(*bind, ty, |c| c.expect(pred, Ty::Bool))
            }
            MapSet { bind, set, elem, .. } | Collect { bind, set, elem } => {
                let dest = match self.shape(e.ty)? {
                    Shape::Set { elem, .. } if matches!(&*e.kind, MapSet { .. }) => {
                        if bitset_universe(elem).is_some() {
                            Ty::Int
                        } else {
                            self.shape_ty(elem)?
                        }
                    }
                    Shape::Seq { elem, .. } if matches!(&*e.kind, Collect { .. }) => self.shape_ty(elem)?,
                    _ => return Err("collection result shape mismatch".into()),
                };
                let ty = self.source(set)?;
                self.bind(*bind, ty, |c| {
                    if let MapSet { cond: Some(cond), .. } = &*e.kind {
                        c.expect(cond, Ty::Bool)?;
                    }
                    c.expect(elem, dest)
                })
            }
            Apply(a, b) => {
                same(e.ty, Ty::Val)?;
                self.expect(a, Ty::Val)?;
                self.expect(b, Ty::Val)
            }
            ValField(x, _) => {
                same(e.ty, Ty::Val)?;
                self.expect(x, Ty::Val)
            }
            Slice { base, loc } => {
                self.expr(base)?;
                self.span(base.ty, *loc, e.ty)
            }
            Index { base, arg, map, slot } => self.index(base, arg, map, *slot, e.ty),
            ExceptAt { base, loc, value } => {
                same(e.ty, base.ty)?;
                self.expr(base)?;
                self.expr(value)?;
                self.span(base.ty, *loc, value.ty)
            }
            ExceptIndex { base, arg, map, slot, value } => {
                same(e.ty, base.ty)?;
                self.expr(value)?;
                self.index(base, arg, map, *slot, value.ty)
            }
            BitMember { set, rank } => {
                same(e.ty, Ty::Bool)?;
                self.expr(set)?;
                self.bitset(set.ty)?;
                self.expect(rank, Ty::Int)
            }
            BitSetOp(_, a, b) => {
                self.bitset(e.ty)?;
                self.expect(a, e.ty)?;
                self.expect(b, e.ty)
            }
            BitCard(x) => {
                same(e.ty, Ty::Int)?;
                self.expr(x)?;
                self.bitset(x.ty)?;
                Ok(())
            }
            Rank(x) => {
                same(e.ty, Ty::Int)?;
                self.expr(x)?;
                self.width(x.ty).map(|_| ())
            }
            Concat(xs) => {
                let mut n = 0usize;
                for x in xs {
                    self.expr(x)?;
                    n = n.checked_add(self.width(x.ty)?).ok_or("concatenation width overflow")?;
                }
                require(n == self.width(e.ty)?, "concatenation width mismatch")
            }
            Pack { locs, parts } => {
                let total = self.width(e.ty)?;
                require(locs.len() == parts.len(), "pack location/part count mismatch")?;
                let mut word_used = vec![0u64; total];
                for (loc, part) in locs.iter().zip(parts.iter()) {
                    self.expr(part)?;
                    let pw = self.width(part.ty)?;
                    match *loc {
                        FieldLoc::Words(off) => {
                            let end = off.checked_add(pw).ok_or("pack word range overflow")?;
                            require(end <= total, "pack word slice outside target")?;
                            for m in &mut word_used[off..end] {
                                require(*m == 0, "pack overlapping target words")?;
                                *m = u64::MAX;
                            }
                        }
                        FieldLoc::Bits(pos) => {
                            require(pw == 1 && self.shape(part.ty)?.is_scalar(), "pack bitfield part width mismatch")?;
                            require(pos.valid_in(total), "pack bitfield outside target")?;
                            let sm = pos.shifted_mask();
                            require(word_used[pos.word] & sm == 0, "pack overlapping bitfields")?;
                            word_used[pos.word] |= sm;
                        }
                    }
                }
                Ok(())
            }
            BitSet(xs) => {
                self.bitset(e.ty)?;
                for x in xs {
                    self.expect(x, Ty::Int)?;
                }
                Ok(())
            }
            SeqLen(x) => {
                same(e.ty, Ty::Int)?;
                self.expr(x)?;
                require(matches!(self.shape(x.ty)?, Shape::Seq { .. }), "sequence length on non-sequence")
            }
            SeqIndex { base, arg, slot } => {
                self.expr(base)?;
                self.expect(arg, Ty::Int)?;
                let (s, _) = self.sequence(base.ty, *slot)?;
                same(e.ty, self.shape_ty(s)?)
            }
            SeqTail { base, slot } | SeqSub { base, slot, .. } | SeqAppend { base, slot, .. } => {
                self.expect(base, e.ty)?;
                let (s, n) = self.sequence(e.ty, *slot)?;
                match &*e.kind {
                    SeqSub { lo, hi, .. } => {
                        self.expect(lo, Ty::Int)?;
                        self.expect(hi, Ty::Int)?;
                    }
                    SeqAppend { value, max_len, .. } => {
                        require(n == *max_len as usize, "sequence capacity mismatch")?;
                        self.expect(value, self.shape_ty(s)?)?;
                    }
                    _ => {}
                }
                Ok(())
            }
            SeqConcat { a, b, slot, max_len } => {
                self.expect(a, e.ty)?;
                self.expect(b, e.ty)?;
                let (_, n) = self.sequence(e.ty, *slot)?;
                require(n == *max_len as usize, "sequence capacity mismatch")
            }
            SeqFilter { bind, seq, pred, slot } => {
                self.expect(seq, e.ty)?;
                let (s, _) = self.sequence(e.ty, *slot)?;
                self.bind(*bind, self.shape_ty(s)?, |c| c.expect(pred, Ty::Bool))
            }
            SortedOp { a, b, elem_words, max_card, .. } => {
                self.expect(a, e.ty)?;
                self.expect(b, e.ty)?;
                let (_, n) = self.sorted(e.ty, *elem_words)?;
                require(n == *max_card as usize, "sorted set capacity mismatch")
            }
            // A constant sorted array of composite encodings (`member_enum`
            // in lower/member.rs): a word array [n, elements...] typed as a
            // sequence of full-width 64-bit integers (a set shape over a small
            // universe would be a bitset); the element is any encoding of
            // that width.
            SortedMember { set, elem, elem_words }
                if matches!(&*set.kind, ExprKind::ConstWords(_))
                    && matches!(self.shape(set.ty), Ok(Shape::Seq { elem: w, .. }) if **w == Shape::Int { lo: i64::MIN, hi: i64::MAX }) =>
            {
                self.expr(set)?;
                let ExprKind::ConstWords(data) = &*set.kind else { unreachable!() };
                let n = data.first().copied().unwrap_or(0) as usize;
                let ew = *elem_words as usize;
                require(
                    ew > 0 && n.checked_mul(ew).and_then(|w| w.checked_add(1)).is_some_and(|w| w <= data.len()),
                    "sorted word array shorter than its elements",
                )?;
                self.expr(elem)?;
                require(self.width(elem.ty)? == ew, "sorted member element width mismatch")?;
                same(e.ty, Ty::Bool)
            }
            SortedMember { set, elem, elem_words } | SortedInsert { set, elem, elem_words, .. } => {
                self.expr(set)?;
                let (s, n) = self.sorted(set.ty, *elem_words)?;
                self.expect(elem, self.shape_ty(s)?)?;
                if let SortedInsert { max_card, .. } = &*e.kind {
                    same(e.ty, set.ty)?;
                    require(n == *max_card as usize, "sorted set capacity mismatch")
                } else {
                    same(e.ty, Ty::Bool)
                }
            }
            UnionField { base, locs } => {
                self.expr(base)?;
                let Shape::Union(arms) = self.shape(base.ty)? else {
                    return Err("union field on non-union".into());
                };
                require(arms.len() == locs.len(), "union arm table length mismatch")?;
                let w = self.width(e.ty)?;
                for (s, loc) in arms.iter().zip(locs.iter()) {
                    if let Some(loc) = loc {
                        let aw = words(s);
                        match *loc {
                            FieldLoc::Words(off) => {
                                require(off.checked_add(w).is_some_and(|end| end <= aw), "union field outside arm")?;
                            }
                            FieldLoc::Bits(pos) => {
                                require(w == 1 && self.shape(e.ty)?.is_scalar(), "union field width mismatch")?;
                                require(pos.valid_in(aw), "union field outside arm")?;
                            }
                        }
                    }
                }
                Ok(())
            }
            UnionFieldInt { base, entries } => {
                same(e.ty, Ty::Int)?;
                self.expr(base)?;
                let Shape::Union(arms) = self.shape(base.ty)? else {
                    return Err("union field on non-union".into());
                };
                require(arms.len() == entries.len(), "union arm table length mismatch")?;
                for (s, entry) in arms.iter().zip(entries.iter()) {
                    if let Some((loc, _)) = entry {
                        let aw = words(s);
                        match *loc {
                            FieldLoc::Words(off) => require(off < aw, "union integer field outside arm")?,
                            FieldLoc::Bits(pos) => require(pos.valid_in(aw), "union integer field outside arm")?,
                        }
                    }
                }
                Ok(())
            }
            RankFlat { x, radices } => {
                same(e.ty, Ty::Int)?;
                self.expr(x)?;
                require(crate::lower::flat_radices(self.shape(x.ty)?).as_deref() == Some(radices.as_ref()), "flat rank radices mismatch")
            }
            RankUnion { x, arms } => {
                same(e.ty, Ty::Int)?;
                self.expr(x)?;
                let expected = crate::lower::union_radices(self.shape(x.ty)?).ok_or("unrankable union")?;
                require(
                    expected.len() == arms.len() && expected.iter().zip(arms.iter()).all(|(a, b)| a.as_slice() == b.as_ref()),
                    "union rank radices mismatch",
                )
            }
            Lookup { x, .. } => {
                same(e.ty, Ty::Int)?;
                self.expr(x)?;
                require(self.shape(x.ty)?.is_scalar(), "lookup argument is not scalar")
            }
            Recode { x, arm_base, table, words: w } => {
                self.expr(x)?;
                require(*w > 0 && *w as usize == self.width(e.ty)?, "recode width mismatch")?;
                require(table.len().is_multiple_of(*w as usize), "recode table width mismatch")?;
                if arm_base.is_empty() {
                    require(self.shape(x.ty)?.is_scalar(), "recode source is not scalar")
                } else {
                    let Shape::Union(arms) = self.shape(x.ty)? else {
                        return Err("recode source is not a union".into());
                    };
                    require(arms.len() == arm_base.len() && arms.iter().all(Shape::is_scalar), "recode union arm mismatch")
                }
            }
            MapGet { base, rank } | MapPut { base, rank, .. } => {
                self.expr(base)?;
                self.expect(rank, Ty::Int)?;
                let Shape::Map { range, .. } = self.shape(base.ty)? else {
                    return Err("map operation on non-map".into());
                };
                if let MapPut { value, .. } = &*e.kind {
                    same(e.ty, base.ty)?;
                    self.expect(value, self.shape_ty(range)?)
                } else {
                    same(e.ty, self.shape_ty(range)?)
                }
            }
            MapBuild { bind, set, rank, value } => {
                let Shape::Map { range, .. } = self.shape(e.ty)? else {
                    return Err("map construction result is not a map".into());
                };
                let result = self.shape_ty(range)?;
                let ty = self.source(set)?;
                self.bind(*bind, ty, |c| {
                    c.expect(rank, Ty::Int)?;
                    c.expect(value, result)
                })
            }
            MapMerge(a, b) => {
                require(matches!(self.shape(e.ty)?, Shape::Map { .. }), "map merge result is not a map")?;
                self.expect(a, e.ty)?;
                self.expect(b, e.ty)
            }
            Enabled(s) => {
                same(e.ty, Ty::Bool)?;
                let assigned = std::mem::replace(&mut self.assigned, vec![false; self.t.var_sid.len()]);
                let partial = std::mem::replace(&mut self.partial, true);
                let result = self.stmt(s);
                self.assigned = assigned;
                self.partial = partial;
                result
            }
            Tuple(xs) => {
                same(e.ty, Ty::Val)?;
                for x in xs {
                    self.expect(x, Ty::Val)?;
                }
                Ok(())
            }
            Call { func, args } => {
                let f = self.t.funcs.get(*func as usize).ok_or("unknown callee")?;
                let needs = &self.contracts[*func as usize];
                require(!needs.current || self.current, "callee reads unavailable current state")?;
                require(
                    needs.next.iter().zip(&self.assigned).all(|(need, assigned)| !need || *assigned),
                    "callee reads unassigned next state",
                )?;
                same(e.ty, f.ret)?;
                require(args.len() == f.params.len(), "call arity mismatch")?;
                for (arg, param) in args.iter().zip(&f.params) {
                    self.expect(arg, *f.temps.get(*param as usize).ok_or("unknown function parameter")?)?;
                }
                Ok(())
            }
            RefOp { op, args } => self.ref_op(e, op, args),
            RefElems(_) => Err("iteration source used as a value".into()),
            ValOp { op, args } => {
                same(e.ty, Ty::Val)?;
                require(op.arity() < 0 || op.arity() as usize == args.len(), "builtin arity mismatch")?;
                for x in args {
                    self.expect(x, Ty::Val)?;
                }
                Ok(())
            }
            Interp { binds, .. } => {
                same(e.ty, Ty::Val)?;
                for (_, x) in binds {
                    self.expr(x)?;
                }
                Ok(())
            }
            Fail(_) => Ok(()),
            ConstElems { .. } | IntRange(..) | Subsets(_) | OrderedSet { .. } => Err("iteration source used as a value".into()),
        }
    }
    fn stmt(&mut self, s: &Stmt) -> Result {
        match s {
            Stmt::Stop | Stmt::Error(_) => Ok(()),
            Stmt::Emit => require(self.partial || self.assigned.iter().all(|x| *x), "emit with unassigned state variables"),
            Stmt::Branches(bs) => {
                for b in bs {
                    self.stmt(b)?;
                }
                Ok(())
            }
            Stmt::Guard { cond, then } => {
                self.expect(cond, Ty::Bool)?;
                self.stmt(then)
            }
            Stmt::Let { temp, value, body } => {
                self.expr(value)?;
                self.bind(*temp, value.ty, |c| c.stmt(body))
            }
            Stmt::ForEach { bind, set, body, .. } => {
                let ty = self.source(set)?;
                self.bind(*bind, ty, |c| c.stmt(body))
            }
            Stmt::Assign { var, value, body } => {
                let ty = self.t.var_sid.get(*var as usize).copied().map(Ty::Enc).ok_or("assignment to unknown variable")?;
                self.expr(value)?;
                // Assignment performs representation conversion when needed.
                if matches!(value.ty, Ty::Enc(_)) {
                    same(value.ty, ty)?;
                }
                let old = std::mem::replace(&mut self.assigned[*var as usize], true);
                let result = self.stmt(body);
                self.assigned[*var as usize] = old;
                result
            }
            Stmt::Repeat { id, bind, set, body, rest } => {
                require(!self.repeats.contains(id), "duplicate active repeat id")?;
                let ty = self.source(set)?;
                self.repeats.push(*id);
                self.bind(*bind, ty, |c| c.stmt(body))?;
                self.repeats.pop();
                self.stmt(rest)
            }
            Stmt::Compose { first, second, paths, .. } => {
                require(self.current, "composition without a current state")?;
                let masks = paths.iter().map(|p| p.assigned.clone()).collect::<Vec<_>>();
                require(masks.iter().all(|m| m.len() == self.assigned.len()), "composition assignment mask length")?;
                require(second.emitted_assignments(self.assigned.len()).as_ref() == Some(&masks), "composition assignment mask mismatch")?;
                let outer = std::mem::replace(&mut self.assigned, vec![false; self.t.var_sid.len()]);
                let partial = std::mem::replace(&mut self.partial, true);
                let result = self.stmt(first).and_then(|_| self.stmt(second));
                self.assigned = outer;
                self.partial = partial;
                result?;
                for path in paths {
                    let outer = self.assigned.clone();
                    for (a, b) in self.assigned.iter_mut().zip(&path.assigned) {
                        *a |= *b;
                    }
                    let result = self.stmt(&path.rest);
                    self.assigned = outer;
                    result?;
                }
                Ok(())
            }
            Stmt::Count(id) => require(self.repeats.contains(id), "count outside its repeat"),
        }
    }
}

/// The verification of a typing's layout and functions (`check_typing`) and
/// the state contracts of its functions, which the checks of actions,
/// predicates, expressions and host regions use: computed once per typing
/// (`Typing::verified_cache`), not once per checked item (a model with many
/// host regions verified each against all functions).
#[derive(Debug, PartialEq)]
pub(crate) struct Verified {
    funcs: usize,
    shapes: usize,
    contracts: Vec<StateContract>,
    /// Whether the encoding width of each shape is its IR width (`words`
    /// walks the shape: checked once per shape, not once per temporary).
    widths: Vec<bool>,
    typing: Result,
}

impl Verified {
    fn parts(&self) -> (&[StateContract], &[bool]) {
        (&self.contracts, &self.widths)
    }
}

fn verified(t: &Typing) -> std::sync::Arc<Verified> {
    verified_with_contracts(t, None)
}

fn verified_with_contracts(t: &Typing, hint: Option<&[StateContract]>) -> std::sync::Arc<Verified> {
    let fresh = || {
        let contracts = hint.map_or_else(|| contracts(t), <[StateContract]>::to_vec);
        let widths: Vec<bool> = (0..t.num_shapes() as ShapeId).map(|s| words(t.shape(s)) == t.words(s) as usize).collect();
        let typing = check_typing(t, (&contracts, &widths));
        std::sync::Arc::new(Verified { funcs: t.funcs.len(), shapes: t.num_shapes(), contracts, widths, typing })
    };
    let cached = t.verified_cache().get_or_init(fresh).clone();
    if cached.funcs != t.funcs.len() || cached.shapes != t.num_shapes() {
        return fresh();
    }
    if cfg!(debug_assertions) || cfg!(test) || tlx_base::knobs::Env::process().flag("TLX_PARANOID") {
        // (A change of `Typing::funcs` must call `Typing::funcs_changed`.)
        assert!(*fresh() == *cached, "stale IR verification of {} functions", t.funcs.len());
    }
    cached
}

/// Verify the state layout and every compiled function, including recursive
/// signatures. No backend may inspect function metadata before this succeeds.
pub fn typing(t: &Typing) -> Result {
    measured(|| verified(t).typing.clone())
}

fn check_typing(t: &Typing, parts: (&[StateContract], &[bool])) -> Result {
    require(t.var_sid.len() == t.layout.vars.len() && t.layout.offsets.len() == t.var_sid.len(), "state layout variable count mismatch")?;
    for sid in t.def_sid.values() {
        require((*sid as usize) < t.num_shapes(), "unknown materialized shape")?;
    }
    let mut offset = 0usize;
    for (i, sid) in t.var_sid.iter().enumerate() {
        require((*sid as usize) < t.num_shapes(), "unknown variable shape")?;
        require(t.shape(*sid) == &t.layout.vars[i], "variable shape differs from layout")?;
        require(t.layout.offsets[i] == offset, "state layout offset mismatch")?;
        offset = offset.checked_add(t.words(*sid) as usize).ok_or("state layout width overflow")?;
    }
    require(offset == t.layout.words, "state layout width mismatch")?;
    for f in &t.funcs {
        let mut c = Check::new(t, parts, &f.temps, Context::Transition)?;
        c.ty(f.ret)?;
        for p in &f.params {
            c.temp(*p)?;
            require(!c.defined[*p as usize], "duplicate function parameter")?;
            c.defined[*p as usize] = true;
        }
        c.expect(&f.body, f.ret).map_err(|e| format!("function {}: {e}", f.name))?;
    }
    Ok(())
}

pub fn action(t: &Typing, f: &ActionFn, context: Context) -> Result {
    measured(|| Check::new(t, verified(t).parts(), &f.temps, context)?.stmt(&f.body).map_err(|e| format!("action {}: {e}", f.name)))
}
pub fn predicate(t: &Typing, p: &PredFn, context: Context) -> Result {
    measured(|| {
        Check::new(t, verified(t).parts(), &p.temps, context)?.expect(&p.body, Ty::Bool).map_err(|e| format!("predicate {}: {e}", p.name))
    })
}
pub fn expression(t: &Typing, temps: &[Ty], inputs: &[Temp], e: &Expr) -> Result {
    measured(|| check_expression(t, temps, inputs, e))
}

fn check_expression(t: &Typing, temps: &[Ty], inputs: &[Temp], e: &Expr) -> Result {
    let v = verified(t);
    let mut c = Check::new(t, v.parts(), temps, Context::Transition)?;
    for p in inputs {
        c.temp(*p)?;
        require(!c.defined[*p as usize], "duplicate region input")?;
        c.defined[*p as usize] = true;
    }
    c.expr(e)
}

fn measured<T>(check: impl FnOnce() -> Result<T>) -> Result<T> {
    let start = std::time::Instant::now();
    let result = check();
    tlx_runtime::stats::add_secs("IR verification", start.elapsed());
    result
}

/// Immutable proof that all IR and layout metadata consumed by a model backend
/// have passed the common verifier. Borrowing prevents mutation until all three
/// backends finish; none can construct this proof themselves.
pub struct Program<'a> {
    typing: &'a Typing,
    init: Option<&'a ActionFn>,
    actions: &'a [Option<ActionFn>],
    predicates: &'a [PredFn],
    transitions: &'a [PredFn],
}

/// An immutable verification input. Lowering supplies its existing function
/// contracts when available; standalone IR callers get the same graph analysis.
pub struct Input<'a> {
    typing: &'a Typing,
    contracts: Option<Vec<StateContract>>,
}
impl<'a> From<&'a Typing> for Input<'a> {
    fn from(typing: &'a Typing) -> Self {
        Self { typing, contracts: None }
    }
}
impl<'a> From<&'a crate::lower::AnalyzedTyping> for Input<'a> {
    fn from(typing: &'a crate::lower::AnalyzedTyping) -> Self {
        Self { typing, contracts: typing.cached_contracts() }
    }
}

impl<'a> Program<'a> {
    pub fn new(
        t: impl Into<Input<'a>>,
        init: Option<&'a ActionFn>,
        actions: &'a [Option<ActionFn>],
        predicates: &'a [PredFn],
        transitions: &'a [PredFn],
    ) -> Result<Self> {
        Self::check(t.into(), init, actions, predicates, transitions, Context::Action)
    }
    pub(crate) fn view(t: &'a Typing, actions: &'a [Option<ActionFn>]) -> Result<Self> {
        Self::check(t.into(), None, actions, &[], &[], Context::Value)
    }
    fn check(
        input: Input<'a>,
        init: Option<&'a ActionFn>,
        actions: &'a [Option<ActionFn>],
        predicates: &'a [PredFn],
        transitions: &'a [PredFn],
        context: Context,
    ) -> Result<Self> {
        let t = input.typing;
        let start = std::time::Instant::now();
        let result = (|| {
            let v = verified_with_contracts(t, input.contracts.as_deref());
            v.typing.clone()?;
            let parts = v.parts();
            if let Some(f) = init {
                Check::new(t, parts, &f.temps, Context::Init)?.stmt(&f.body).map_err(|e| format!("Init {}: {e}", f.name))?;
            }
            for f in actions.iter().flatten() {
                Check::new(t, parts, &f.temps, context)?.stmt(&f.body).map_err(|e| format!("action {}: {e}", f.name))?;
            }
            for p in predicates {
                Check::new(t, parts, &p.temps, Context::State)?
                    .expect(&p.body, Ty::Bool)
                    .map_err(|e| format!("predicate {}: {e}", p.name))?;
            }
            for p in transitions {
                Check::new(t, parts, &p.temps, Context::Transition)?
                    .expect(&p.body, Ty::Bool)
                    .map_err(|e| format!("transition {}: {e}", p.name))?;
            }
            Ok(Self { typing: t, init, actions, predicates, transitions })
        })();
        tlx_runtime::stats::add_secs("IR verification", start.elapsed());
        result
    }
    pub fn typing(&self) -> &'a Typing {
        self.typing
    }
    pub fn init(&self) -> Option<&'a ActionFn> {
        self.init
    }
    pub fn actions(&self) -> &'a [Option<ActionFn>] {
        self.actions
    }
    pub fn predicates(&self) -> &'a [PredFn] {
        self.predicates
    }
    pub fn transitions(&self) -> &'a [PredFn] {
        self.transitions
    }
}

/// Invalid compiler IR is a compiler bug. Development/paranoid runs fail hard;
/// production rejects the compilation unit and uses its interpreter fallback.
pub(crate) fn enforce<T>(result: Result<T>) -> Result<T> {
    if let Err(e) = &result {
        assert!(!hard_errors(), "invalid typed IR: {e}");
    }
    result
}

fn hard_errors() -> bool {
    cfg!(debug_assertions)
        || cfg!(test)
        || tlx_base::knobs::Env::process().flag("TLX_PARANOID")
        || tlx_base::knobs::Env::process().flag("TLX_IR_VERIFY_HARD")
}

/// Check a host region before deriving its ABI signature. Input order is part
/// of the ABI; each listed temp must exist exactly once and cover all free uses.
pub fn region(t: &Typing, r: &crate::enc::mixed::Region) -> Result {
    measured(|| check_region(t, r))
}

fn check_region(t: &Typing, r: &crate::enc::mixed::Region) -> Result {
    use crate::enc::mixed::RegionCtx;
    let context = match r.ctx {
        RegionCtx::Init => Context::Init,
        RegionCtx::Action => Context::Action,
        RegionCtx::StatePred => Context::State,
        RegionCtx::TransPred => Context::Transition,
    };
    let v = verified(t);
    let mut c = Check::new(t, v.parts(), &r.temps, context)?;
    if matches!(r.ctx, RegionCtx::Init | RegionCtx::Action) {
        require(r.assigned.len() == t.var_sid.len(), "region assignment contract size mismatch")?;
        c.assigned.copy_from_slice(&r.assigned);
    }
    // Init's host interpreter sees its partially constructed next state as s0.
    // Lowered expressions themselves use NextVar, as in the enclosing Init.
    for &p in &r.inputs {
        c.temp(p)?;
        require(!c.defined[p as usize], "duplicate region input")?;
        c.defined[p as usize] = true;
    }
    let free = crate::lower::free_temps(&r.expr);
    require(free.len() == r.inputs.len() && free.iter().all(|p| r.inputs.contains(p)), "region inputs differ from free temporaries")?;
    if let Some(reads) = &r.info.reads {
        for &v in reads.cur.iter().chain(&reads.next) {
            require((v as usize) < t.var_sid.len(), "region reads unknown variable")?;
        }
        // Read summaries are conservative: they can include next variables
        // local to an ENABLED inside an interpreter fallback. Actual IR
        // NextVar uses are checked by the scoped expression traversal below.
    }
    c.expr(&r.expr)
}

#[cfg(test)]
#[path = "verify_tests.rs"]
mod tests;

/// The caller and host must agree on both sides of the region ABI, even when
/// a separately supplied native plan is used by a second backend.
pub(crate) fn region_call(r: &crate::enc::mixed::Region, temps: &[Ty], result: Ty, context: crate::enc::mixed::RegionCtx) -> Result {
    same(r.expr.ty, result)?;
    require(r.ctx == context, "region caller state context mismatch")?;
    for &p in &r.inputs {
        let expected = temps.get(p as usize).ok_or("region input outside caller frame")?;
        let actual = r.temps.get(p as usize).ok_or("region input outside region frame")?;
        same(*actual, *expected)?;
    }
    Ok(())
}
