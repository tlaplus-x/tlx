//! Typed IR of the compiled tier (design.md §6.3).
//!
//! An action instance is lowered to a statement tree in continuation-passing
//! form that mirrors TLC's enumeration (enumerate.rs): which next-state
//! variables are assigned at each point is known statically, disjunctions
//! duplicate their continuation, and `Emit` appears exactly where the
//! interpreter would emit a successor.
//!
//! Expressions are typed with a *representation* (`Ty`): scalars are
//! unboxed, values of state variables keep their layout encoding (`Enc`), and
//! everything else falls back to boxed `tlx_value::Value`s (`Val`), evaluated
//! with the value library or, as a last resort, by the interpreter
//! (`ExprKind::Interp`).

use std::sync::Arc;

use tlx_eval::env::Env;
pub use tlx_layout::layout::{BitPos, FieldLayout, FieldLoc, SlotLayout};
use tlx_sema::hir;
use tlx_value::plan::Absent;
use tlx_value::Value;

pub use crate::coverage::{boxed_histogram_typed, Coverage};

pub(crate) mod encoding;

#[cfg(test)]
mod metadata_tests;

/// Index into the shape registry (`types::Typing`).
pub type ShapeId = u32;
/// IR temporary (local of an action/predicate function).
pub type Temp = u32;

/// Runtime representation of an IR value.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Ty {
    Bool,
    /// i64 with TLC's 32-bit overflow checks on arithmetic.
    Int,
    /// Encoded per the layout of a shape (`words(shape)` u64 words).
    Enc(ShapeId),
    /// Boxed dynamic value.
    Val,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IntOp {
    Add,
    Sub,
    Mul,
    /// `\div` as overridden by Integers (floor division).
    DivFloor,
    /// `\div` as overridden by Naturals (TLC's truncation quirk).
    DivNat,
    /// `a ^ b` (b natural, 32-bit overflow checked).
    Pow,
    /// DyadicRationals' GCD (`arith::gcd`: commons-math gcd, as TLC's Reduce).
    Gcd,
    Mod,
}

/// How a function argument selects a slot of an encoded function/tuple.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IndexMap {
    /// Integer argument in `lo..lo+n`: slot `arg - lo`.
    IntRange { lo: i64, n: u32 },
    /// Encoded atom argument (index into its universe): slot `table[idx]`
    /// (-1 = not in the domain).
    Table(Arc<[i32]>),
}

/// The value plan (`tlx_value::plan`) of a map update (`ExprKind::MapPut`),
/// computed once by lowering (`Typing::map_put_plan`); C, JIT and the
/// closure executor read it instead of deriving the rule themselves.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MapPutPlan {
    /// `Absent::Unchanged` (EXCEPT) or `Absent::Insert` (`:>`, `@@`).
    pub absent: Absent,
    /// Key ranks that an EXCEPT on an empty map rejects although they are
    /// absent: an empty map decodes as `<<>>`, whose witness admits only
    /// integer keys (`Witness::Tuple.key_type()`). Empty for inserts.
    pub reject_when_empty: Arc<[std::ops::Range<u64>]>,
}

impl MapPutPlan {
    pub fn inserts(&self) -> bool {
        self.absent == Absent::Insert
    }
}

/// An operation on value store handles (`ExprKind::RefOp`): what the
/// method of `tlx_layout::store::Store` of the same name computes, which
/// mirrors the interpreter's operation (a different result is never
/// produced; a case the store does not mirror is a runtime error, and the
/// interpreter redoes the call). Handles are `Ty::Enc` of the run's `Ref`
/// shape (`Typing::ref_sid`).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum RefOp {
    /// `DOMAIN f`: handle -> handle.
    Domain,
    /// `f[k]` (absent: error): handles -> handle.
    Apply,
    /// The index of key `k` in function `f`'s view, -1 if absent (a key
    /// the witness rejects: error): handles -> Int.
    Select,
    /// The value at index `i` of `f`'s view: handle, Int -> handle.
    ValueAt,
    /// `f` with the value at index `i` replaced by `v`: handle, Int,
    /// handle -> handle.
    SetAt,
    /// `k :> v`: handles -> handle.
    Single,
    /// `f @@ g`: handles -> handle.
    Merge,
    /// `x \in S`: handles -> Bool.
    Member,
    /// `k \in DOMAIN f`: handles -> Bool.
    InDomain,
    /// `r.name`: handle -> handle.
    Field(tlx_value::Sym),
    /// `Cardinality(S)`: handle -> Int.
    Cardinality,
    /// `Len(s)`: handle -> Int.
    Len,
    /// `Append(s, x)`: handles -> handle.
    Append,
    /// `Head(s)`, `Tail(s)`: handle -> handle.
    Head,
    Tail,
    /// `<<x1, ..., xn>>`: handles -> handle.
    Tuple,
    /// `[f1 |-> x1, ...]` (the names in the order of the arguments):
    /// handles -> handle.
    Record(Arc<[tlx_value::Sym]>),
    /// TLA+ `=` (TLC's equality, with its errors): handles -> Bool.
    Eq,
    /// The handle of an integer / Boolean: Int or Bool -> handle.
    FromInt,
    FromBool,
    /// The integer / Boolean of a handle (any other value: error).
    ToInt,
    ToBool,
    /// A value of encoding `.0` as a handle: Enc(.0) -> handle.
    FromEnc(ShapeId),
    /// A handle's value in encoding `.0` (a value outside it: error):
    /// handle -> Enc(.0).
    ToEnc(ShapeId),
}

/// Bitset operations on two sets of the same shape.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SetOp {
    Union,
    Inter,
    Diff,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CmpOp {
    Lt,
    Le,
    Gt,
    Ge,
}

#[derive(Clone, Debug)]
pub struct Expr {
    pub ty: Ty,
    pub kind: Box<ExprKind>,
}

#[derive(Clone, Debug)]
pub enum ExprKind {
    /// A constant (folded at compile time); `ty` says how it is represented
    /// (for `Enc` types the value is encoded on use; see `ConstWords`).
    Const(Value),
    /// A constant already encoded in the layout of `ty` (an `Enc` type).
    ConstWords(Arc<[u64]>),
    /// Current-state variable.
    Var(u32),
    /// Next-state variable (statically known to be assigned).
    NextVar(u32),
    Temp(Temp),

    Not(Expr),
    /// Short-circuit conjunction / disjunction of booleans.
    And(Vec<Expr>),
    Or(Vec<Expr>),
    If(Expr, Expr, Expr),
    IntBin(IntOp, Expr, Expr),
    IntCmp(CmpOp, Expr, Expr),
    Neg(Expr),
    /// Equality of two operands of the same `Ty` (TLC semantics for `Val`).
    Eq(Expr, Expr),

    /// Convert between representations (`Enc`/scalar → `Val` always works;
    /// `Val` → `Enc`/scalar may fail with a layout miss or a type error).
    Convert(Expr),

    /// `\E` / `\A` over the elements of a set (in enumeration order),
    /// binding each element to `bind`.
    Exists {
        bind: Temp,
        set: Expr,
        body: Expr,
    },
    Forall {
        bind: Temp,
        set: Expr,
        body: Expr,
    },
    /// `CHOOSE bind \in set : body` (TLC order).
    Choose {
        bind: Temp,
        set: Expr,
        body: Expr,
    },
    /// `LET temp == value IN body` (evaluated eagerly).
    Let {
        temp: Temp,
        value: Expr,
        body: Expr,
    },

    /// `f[arg]` on boxed values.
    Apply(Expr, Expr),
    /// `r.f` on a boxed record.
    ValField(Expr, tlx_value::Sym),

    // ---- encoded (layout) operations ----
    /// Sub-encoding at a fixed word or bit location (record field, constant
    /// function argument); `ty` is the field's `Enc` type.
    Slice {
        base: Expr,
        loc: FieldLoc,
    },
    /// `f[arg]` on an encoded function/tuple with homogeneous slots; out of
    /// domain = runtime error.
    Index {
        base: Expr,
        arg: Expr,
        map: IndexMap,
        slot: SlotLayout,
    },
    /// `[f EXCEPT ![k] = v]` at a fixed word or bit location (`v` already has
    /// the slot's type).
    ExceptAt {
        base: Expr,
        loc: FieldLoc,
        value: Expr,
    },
    /// `[f EXCEPT ![arg] = v]` with a computed slot.
    ExceptIndex {
        base: Expr,
        arg: Expr,
        map: IndexMap,
        slot: SlotLayout,
        value: Expr,
    },
    /// Membership of an element given by its rank in a bitset of `ty`'s set shape.
    BitMember {
        set: Expr,
        rank: Expr,
    },
    /// Union / intersection / difference of two bitsets of the same shape.
    BitSetOp(SetOp, Expr, Expr),
    /// Number of elements of a bitset.
    BitCard(Expr),
    /// Rank of an encoded scalar within its shape (Int: v - lo, Atom/Bool: the word).
    Rank(Expr),
    /// Concatenation of word-aligned encodings (`ty` is the result).
    Concat(Vec<Expr>),
    /// Packed composite construction: zero-initializes the result words of
    /// `ty` and stores each part at `locs[i]`.
    Pack {
        locs: Arc<[FieldLoc]>,
        parts: Vec<Expr>,
    },
    /// Bitset with the given element ranks set (set construction); `ty` is the set.
    BitSet(Vec<Expr>),
    /// `Len(s)` of an encoded sequence.
    SeqLen(Expr),
    /// `s[i]` (1-based, checked against the length) of an encoded sequence.
    SeqIndex {
        base: Expr,
        arg: Expr,
        slot: SlotLayout,
    },
    /// `Tail(s)` (error if empty).
    SeqTail {
        base: Expr,
        slot: SlotLayout,
    },
    /// `Append(s, x)` (`x` in the element encoding; error if the layout's
    /// maximum length would be exceeded).
    SeqAppend {
        base: Expr,
        value: Expr,
        slot: SlotLayout,
        max_len: u32,
    },
    /// `SubSeq(base, lo, hi)` (same sequence encoding as `base`).
    SeqSub {
        base: Expr,
        lo: Expr,
        hi: Expr,
        slot: SlotLayout,
    },
    /// `a \cup b` / `a \cap b` / `a \ b` for sorted-array sets of the
    /// node's encoding (a merge).
    SortedOp {
        op: SetOp,
        a: Expr,
        b: Expr,
        elem_words: u32,
        max_card: u32,
    },
    /// `SelectSeq(seq, LAMBDA bind : pred)` (same encoding as `seq`).
    SeqFilter {
        bind: Temp,
        seq: Expr,
        pred: Expr,
        slot: SlotLayout,
    },
    /// `a \o b` (both in the node's sequence encoding).
    SeqConcat {
        a: Expr,
        b: Expr,
        slot: SlotLayout,
        max_len: u32,
    },
    /// Field of a union of records: `locs[arm]` is the field's location
    /// within that arm's encoding (None = arm has no such field: error).
    /// `ty` is the field's (common) encoded type.
    UnionField {
        base: Expr,
        locs: Arc<[Option<FieldLoc>]>,
    },
    /// Integer field of a union of records whose arms encode it with
    /// different ranges: per arm (location, lo).
    UnionFieldInt {
        base: Expr,
        entries: Arc<[Option<(FieldLoc, i64)>]>,
    },
    /// A sorted-array set iterated in TLC order, keeping elements encoded.
    OrderedSet {
        set: Expr,
        plan: Arc<[u64]>,
    },
    /// The elements of a constant set, encoded and listed in TLC order.
    ConstElems {
        elem: ShapeId,
        words: Arc<[u64]>,
        count: u32,
    },
    /// The integers `lo..hi` (both `Ty::Int`); only used as an iteration
    /// source, binding unboxed integers.
    IntRange(Expr, Expr),
    /// The subsets of the encoded bitset `x` (bitsets of `x`'s shape), by
    /// size, then lexicographically by element rank (TLC's order for
    /// `SUBSET`); only used as an iteration source.
    Subsets(Expr),
    /// A runtime error (the compiled evaluation bails out to the interpreter,
    /// which reports it exactly).
    Fail(Arc<str>),
    /// `{bind \in set : pred}` on an encoded set (same shape as `set`).
    Filter {
        bind: Temp,
        set: Expr,
        pred: Expr,
    },
    /// `{elem : bind \in set}` built into the encoded set shape of the node
    /// (`set` is any typed iteration source; `elem` has the element shape).
    /// With `cond`, only elements for which it holds are included.
    MapSet {
        bind: Temp,
        set: Expr,
        elem: Expr,
        cond: Option<Expr>,
    },
    /// The sequence (in the node's `Seq` encoding) of `elem` for each
    /// element of the iteration source `set` bound to `bind`, in iteration
    /// order (more elements than the capacity: runtime error).
    Collect {
        bind: Temp,
        set: Expr,
        elem: Expr,
    },
    /// The sum (or, with `product`, the product) of the integer `body` over
    /// the elements of the iteration source `set` bound to `bind`; a
    /// product stops at the first zero (the remaining elements are not
    /// evaluated).
    Fold {
        product: bool,
        bind: Temp,
        set: Expr,
        body: Expr,
    },
    /// The union of the encoded bitsets `body` over the iteration source
    /// `set` bound to `bind`, in iteration order (the node's own bitset
    /// shape). Every element is evaluated, as TLC builds the set of sets
    /// before taking its union.
    UnionFold {
        bind: Temp,
        set: Expr,
        body: Expr,
    },
    /// Rank of an encoded flat product (tuple/record of scalars, one word
    /// per component, each word its component's rank): mixed radix with the
    /// first component most significant (as `layout::rank`).
    RankFlat {
        x: Expr,
        radices: Arc<[u64]>,
    },
    /// Re-encode a scalar / union-of-scalars value: its code (`x[0]`, or
    /// `arm_base[x[0]] + x[1]` for a union source) indexes `table`, which
    /// holds `words` target words per code (`u64::MAX` first word = the value
    /// does not fit the target: runtime error).
    Recode {
        x: Expr,
        arm_base: Arc<[u64]>,
        table: Arc<[u64]>,
        words: u32,
    },
    /// Rank of an encoded union whose arms are scalars or flat products:
    /// the cardinalities of the arms before `x`'s arm plus the mixed-radix
    /// rank of its payload (`arms[i]` = radices of arm i; as `layout::rank`).
    RankUnion {
        x: Expr,
        arms: Arc<[Arc<[u64]>]>,
    },
    /// `table[rank(x)]` for an encoded scalar `x` (-1 marks "absent").
    Lookup {
        x: Expr,
        table: Arc<[i32]>,
    },
    /// Membership in a sorted-array set (binary search over encodings).
    SortedMember {
        set: Expr,
        elem: Expr,
        elem_words: u32,
    },
    /// Insert an element into a sorted-array set (error if `max_card` would
    /// be exceeded).
    SortedInsert {
        set: Expr,
        elem: Expr,
        elem_words: u32,
        max_card: u32,
    },
    /// `m[k]` on an encoded map (`Shape::Map`, see `types::map_dims`):
    /// the slot of the key of rank `rank` in the key universe (an absent
    /// key or a rank outside the universe is a runtime error). `ty` is the
    /// range's encoding.
    MapGet {
        base: Expr,
        rank: Expr,
    },
    /// The map `base` (of `ty`'s shape) with the key of rank `rank` mapped
    /// to `value` (in the range encoding), following `plan`: with
    /// `Absent::Unchanged` this is `[base EXCEPT ![k] = value]` (an absent
    /// key leaves `base` unchanged, as in TLC, and `value` is not
    /// evaluated, except for the keys the plan rejects); with
    /// `Absent::Insert` the key is added if absent (`k :> v`, `@@`), and a
    /// rank outside the universe is a runtime error.
    MapPut {
        base: Expr,
        rank: Expr,
        value: Expr,
        plan: MapPutPlan,
    },
    /// `[bind \in set |-> value]` built into the map shape of `ty`: for
    /// each element of the iteration source `set`, `rank` (of the key bound
    /// to `bind`; outside the universe = runtime error) and `value` (in the
    /// range encoding) define one entry; all other slots are zero.
    MapBuild {
        bind: Temp,
        set: Expr,
        rank: Expr,
        value: Expr,
    },
    /// `f @@ g` on two maps of `ty`'s shape (`f`'s entries take precedence).
    MapMerge(Expr, Expr),
    /// `ENABLED A`: whether running the statement tree of `A` (over the
    /// current state and a fresh next state; the end of any path emits,
    /// assigned or not, as in TLC) emits a state. Stops at the first one.
    Enabled(Box<Stmt>),
    /// `<<e1, ..., en>>`
    Tuple(Vec<Expr>),
    /// Call of compiled function `func` (`Typing::funcs`, e.g. a RECURSIVE
    /// operator) with arguments in its parameter representations; `ty` is
    /// its result representation.
    Call {
        func: u32,
        args: Vec<Expr>,
    },
    /// An operation on value store handles (`RefOp`; the arguments in
    /// the representations it states, evaluated in order).
    RefOp {
        op: RefOp,
        args: Vec<Expr>,
    },
    /// The elements of the stored set `.0` (a handle), in normalized order;
    /// only used as an iteration source, binding handles.
    RefElems(Expr),
    /// Built-in operator on boxed values (tlx-value ops / interpreter builtins).
    ValOp {
        op: tlx_sema::builtins::Builtin,
        args: Vec<Expr>,
    },
    /// Fallback: evaluate an HIR expression with the interpreter. The
    /// environment is `env` (constant bindings), then `binds` (runtime values
    /// of IR-bound locals), then `deferred` (call-by-name arguments and
    /// operator arguments, bound in order, each closing over everything bound
    /// before it). A local of `binds` that is a `def_value_key` hands the
    /// value of that definition in the current or next state to the
    /// interpreter (computed by the IR, see `Lowerer::wrap_materialized`).
    Interp {
        expr: hir::Expr,
        binds: Vec<(hir::LocalId, Expr)>,
        deferred: Vec<Deferred>,
        env: Env,
    },
}

/// A binding of an `Interp` environment that is not a value.
#[derive(Clone, Debug)]
pub enum Deferred {
    /// Call-by-name argument (evaluated on use).
    Thunk(hir::LocalId, hir::Expr),
    /// Call-by-name argument with one value per context (deterministic,
    /// not action-level): evaluated on first use, at most once per
    /// evaluation of the fallback (the interpreter evaluates the arguments
    /// of such calls once).
    Once(hir::LocalId, hir::Expr),
    /// `LAMBDA params : body` operator argument.
    Lambda(hir::LocalId, Arc<[hir::LocalId]>, hir::Expr),
    /// Named operator passed as an argument.
    OpRef(hir::LocalId, hir::OpRef),
}

/// Statement tree of an action / init enumeration (CPS form).
#[derive(Clone, Debug)]
pub enum Stmt {
    /// Prune this branch.
    Stop,
    /// All variables are assigned: emit the next state.
    Emit,
    /// Run each branch in order (disjunction; each branch has its own copy
    /// of the continuation).
    Branches(Vec<Stmt>),
    /// Continue with `then` if `cond` holds, else stop.
    Guard { cond: Expr, then: Box<Stmt> },
    /// Bind `temp` and continue.
    Let { temp: Temp, value: Expr, body: Box<Stmt> },
    /// For each element of `set` bind `bind`, run `body`. Elements come in
    /// TLC enumeration order, or sorted (normalized) order if `sorted`.
    ForEach { bind: Temp, set: Expr, sorted: bool, body: Box<Stmt> },
    /// Assign next-state variable `var` (encoded into its layout; a value
    /// outside the layout is a layout miss) and continue.
    Assign { var: u32, value: Expr, body: Box<Stmt> },
    /// Runtime error when reached (TLC reports it only if the path executes).
    Error(Arc<str>),
    /// TLC expands `\A x \in S : B` in an action into `B[x1] /\ B[x2] ...`;
    /// when B cannot assign, every path through B leaves the same
    /// continuation, so this runs `rest` (product over the elements of the
    /// number of paths through `body`) times. `body` ends in `Count(id)`.
    Repeat { id: u32, bind: Temp, set: Expr, body: Box<Stmt>, rest: Box<Stmt> },
    /// Sequential composition. Both actions enumerate independent partial
    /// states; missing first-step variables retain their current values.
    /// Each second-step assignment mask selects its continuation, which
    /// executes in the original context after merging compatible values.
    Compose { first: Box<Stmt>, second: Box<Stmt>, paths: Vec<ComposePath>, count: bool },
    /// A path through the body of `Repeat` `id` completed.
    Count(u32),
}

/// Continuation for one assignment mask of a composition's second step.
#[derive(Clone, Debug)]
pub struct ComposePath {
    pub assigned: Vec<bool>,
    pub rest: Stmt,
}

/// A compiled function (a RECURSIVE operator or recursive function
/// definition specialized to the representations of its arguments): its
/// parameters are temps of its own frame, evaluated before the body.
#[derive(Clone, Debug)]
pub struct FnDef {
    pub name: Arc<str>,
    pub params: Vec<Temp>,
    pub temps: Vec<Ty>,
    pub ret: Ty,
    pub body: Expr,
    /// Calls of it count against a budget per outermost call (a recursive
    /// function definition: TLC caches its points, the compiled function
    /// recomputes them; beyond the budget the interpreter takes over).
    pub budgeted: bool,
}

/// A lowered action instance.
#[derive(Clone, Debug)]
pub struct ActionFn {
    pub name: Arc<str>,
    pub temps: Vec<Ty>,
    pub body: Stmt,
}

/// A lowered predicate (invariant over a state, action property over a
/// transition).
#[derive(Clone, Debug)]
pub struct PredFn {
    pub name: Arc<str>,
    pub temps: Vec<Ty>,
    pub body: Expr,
}

impl Expr {
    /// Whether this IR expression contains an `ENABLED`, including in
    /// interpreter runtime bindings. Opaque HIR and deferred bindings remain
    /// interpreter-owned, as in `for_each_child`.
    pub(crate) fn contains_enabled(&self) -> bool {
        let mut found = matches!(&*self.kind, ExprKind::Enabled(_));
        if !found {
            self.for_each_child(&mut |child| found = found || child.contains_enabled());
        }
        found
    }

    pub(crate) fn has_composition(&self) -> bool {
        let mut found = matches!(&*self.kind, ExprKind::Enabled(s) if s.has_composition());
        self.for_each_child(&mut |e| found |= e.has_composition());
        found
    }

    pub(crate) fn has_boxed_operand(&self) -> bool {
        use ExprKind as K;
        if matches!(&*self.kind, K::Let { .. } | K::If(..) | K::Eq(..) | K::Convert(_) | K::Enabled(_) | K::Fail(_) | K::Temp(_)) {
            return false;
        }
        let mut found = false;
        self.for_each_child(&mut |child| found |= child.ty == Ty::Val && !child.is_typed_source());
        found
    }

    pub fn new(ty: Ty, kind: ExprKind) -> Expr {
        Expr { ty, kind: Box::new(kind) }
    }

    /// An iteration source yielding typed (encoded or integer) elements.
    pub fn is_typed_source(&self) -> bool {
        matches!(self.ty, Ty::Enc(_))
            || matches!(
                &*self.kind,
                ExprKind::ConstElems { .. }
                    | ExprKind::IntRange(..)
                    | ExprKind::Subsets(_)
                    | ExprKind::OrderedSet { .. }
                    | ExprKind::RefElems(_)
            )
    }

    /// Call `f` on every direct sub-expression (in evaluation order).
    pub fn for_each_child(&self, f: &mut dyn FnMut(&Expr)) {
        use ExprKind::*;
        match &*self.kind {
            Const(_) | ConstWords(_) | ConstElems { .. } | Fail(_) | Var(_) | NextVar(_) | Temp(_) => {}
            Not(x) | Neg(x) | Convert(x) | Subsets(x) | BitCard(x) | Rank(x) | SeqLen(x) | ValField(x, _) | RefElems(x) => f(x),
            Slice { base, .. }
            | SeqTail { base, .. }
            | UnionField { base, .. }
            | UnionFieldInt { base, .. }
            | RankFlat { x: base, .. }
            | Lookup { x: base, .. }
            | Recode { x: base, .. }
            | RankUnion { x: base, .. }
            | OrderedSet { set: base, .. } => f(base),
            And(xs)
            | Or(xs)
            | Tuple(xs)
            | Concat(xs)
            | Pack { parts: xs, .. }
            | BitSet(xs)
            | ValOp { args: xs, .. }
            | RefOp { args: xs, .. }
            | Call { args: xs, .. } => xs.iter().for_each(f),
            If(a, b, c) => {
                f(a);
                f(b);
                f(c);
            }
            IntBin(_, a, b) | IntCmp(_, a, b) | Eq(a, b) | Apply(a, b) | BitSetOp(_, a, b) | IntRange(a, b) => {
                f(a);
                f(b);
            }
            Index { base: a, arg: b, .. }
            | SeqIndex { base: a, arg: b, .. }
            | ExceptAt { base: a, value: b, .. }
            | SeqAppend { base: a, value: b, .. }
            | SeqConcat { a, b, .. }
            | BitMember { set: a, rank: b }
            | SortedMember { set: a, elem: b, .. }
            | SortedInsert { set: a, elem: b, .. }
            | Exists { set: a, body: b, .. }
            | Forall { set: a, body: b, .. }
            | Choose { set: a, body: b, .. }
            | Filter { set: a, pred: b, .. }
            | Let { value: a, body: b, .. }
            | MapGet { base: a, rank: b }
            | MapMerge(a, b) => {
                f(a);
                f(b);
            }
            MapPut { base, rank, value, .. } => {
                f(base);
                f(rank);
                f(value);
            }
            MapBuild { set, rank, value, .. } => {
                f(set);
                f(rank);
                f(value);
            }
            SeqSub { base, lo, hi, .. } => {
                f(base);
                f(lo);
                f(hi);
            }
            SortedOp { a, b, .. } => {
                f(a);
                f(b);
            }
            SeqFilter { seq, pred, .. } => {
                f(seq);
                f(pred);
            }
            Fold { set, body, .. } | UnionFold { set, body, .. } => {
                f(set);
                f(body);
            }
            Collect { set, elem, .. } => {
                f(set);
                f(elem);
            }
            MapSet { set, elem, cond, .. } => {
                f(set);
                if let Some(c) = cond {
                    f(c);
                }
                f(elem);
            }
            ExceptIndex { base, arg, value, .. } => {
                f(base);
                f(arg);
                f(value);
            }
            Interp { binds, .. } => binds.iter().for_each(|(_, x)| f(x)),
            Enabled(s) => s.for_each_expr_deep(f),
        }
    }

    /// `for_each_child` with mutable access (same children, same order;
    /// for `Enabled`, the expressions of its statement tree).
    pub fn for_each_child_mut(&mut self, f: &mut dyn FnMut(&mut Expr)) {
        use ExprKind::*;
        match &mut *self.kind {
            Const(_) | ConstWords(_) | ConstElems { .. } | Fail(_) | Var(_) | NextVar(_) | Temp(_) => {}
            Not(x) | Neg(x) | Convert(x) | Subsets(x) | BitCard(x) | Rank(x) | SeqLen(x) | ValField(x, _) | RefElems(x) => f(x),
            Slice { base, .. }
            | SeqTail { base, .. }
            | UnionField { base, .. }
            | UnionFieldInt { base, .. }
            | RankFlat { x: base, .. }
            | Lookup { x: base, .. }
            | Recode { x: base, .. }
            | RankUnion { x: base, .. }
            | OrderedSet { set: base, .. } => f(base),
            And(xs)
            | Or(xs)
            | Tuple(xs)
            | Concat(xs)
            | Pack { parts: xs, .. }
            | BitSet(xs)
            | ValOp { args: xs, .. }
            | RefOp { args: xs, .. }
            | Call { args: xs, .. } => xs.iter_mut().for_each(f),
            If(a, b, c) => {
                f(a);
                f(b);
                f(c);
            }
            IntBin(_, a, b) | IntCmp(_, a, b) | Eq(a, b) | Apply(a, b) | BitSetOp(_, a, b) | IntRange(a, b) => {
                f(a);
                f(b);
            }
            Index { base: a, arg: b, .. }
            | SeqIndex { base: a, arg: b, .. }
            | ExceptAt { base: a, value: b, .. }
            | SeqAppend { base: a, value: b, .. }
            | SeqConcat { a, b, .. }
            | BitMember { set: a, rank: b }
            | SortedMember { set: a, elem: b, .. }
            | SortedInsert { set: a, elem: b, .. }
            | Exists { set: a, body: b, .. }
            | Forall { set: a, body: b, .. }
            | Choose { set: a, body: b, .. }
            | Filter { set: a, pred: b, .. }
            | Let { value: a, body: b, .. }
            | MapGet { base: a, rank: b }
            | MapMerge(a, b)
            | SortedOp { a, b, .. }
            | SeqFilter { seq: a, pred: b, .. }
            | Fold { set: a, body: b, .. }
            | UnionFold { set: a, body: b, .. }
            | Collect { set: a, elem: b, .. } => {
                f(a);
                f(b);
            }
            MapPut { base: a, rank: b, value: c, .. }
            | MapBuild { set: a, rank: b, value: c, .. }
            | SeqSub { base: a, lo: b, hi: c, .. }
            | ExceptIndex { base: a, arg: b, value: c, .. } => {
                f(a);
                f(b);
                f(c);
            }
            MapSet { set, elem, cond, .. } => {
                f(set);
                if let Some(c) = cond {
                    f(c);
                }
                f(elem);
            }
            Interp { binds, .. } => binds.iter_mut().for_each(|(_, x)| f(x)),
            Enabled(s) => s.for_each_expr_deep_mut(f),
        }
    }
}

impl Stmt {
    /// The expression this statement evaluates itself (before running any
    /// sub-statement), if any.
    pub fn expr(&self) -> Option<&Expr> {
        match self {
            Stmt::Stop | Stmt::Emit | Stmt::Branches(_) | Stmt::Error(_) | Stmt::Count(_) | Stmt::Compose { .. } => None,
            Stmt::Guard { cond: e, .. }
            | Stmt::Let { value: e, .. }
            | Stmt::ForEach { set: e, .. }
            | Stmt::Assign { value: e, .. }
            | Stmt::Repeat { set: e, .. } => Some(e),
        }
    }

    /// Call `f` on the expression of every statement of the tree.
    pub fn for_each_expr_deep(&self, f: &mut dyn FnMut(&Expr)) {
        if let Some(e) = self.expr() {
            f(e);
        }
        self.for_each_sub_stmt(&mut |b| b.for_each_expr_deep(f));
    }

    /// `expr` with mutable access.
    fn expr_mut(&mut self) -> Option<&mut Expr> {
        match self {
            Stmt::Stop | Stmt::Emit | Stmt::Branches(_) | Stmt::Error(_) | Stmt::Count(_) | Stmt::Compose { .. } => None,
            Stmt::Guard { cond: e, .. }
            | Stmt::Let { value: e, .. }
            | Stmt::ForEach { set: e, .. }
            | Stmt::Assign { value: e, .. }
            | Stmt::Repeat { set: e, .. } => Some(e),
        }
    }

    /// `for_each_expr_deep` with mutable access.
    pub fn for_each_expr_deep_mut(&mut self, f: &mut dyn FnMut(&mut Expr)) {
        if let Some(e) = self.expr_mut() {
            f(e);
        }
        self.for_each_sub_stmt_mut(&mut |b| b.for_each_expr_deep_mut(f));
    }

    /// `for_each_sub_stmt` with mutable access.
    fn for_each_sub_stmt_mut(&mut self, f: &mut dyn FnMut(&mut Stmt)) {
        match self {
            Stmt::Stop | Stmt::Emit | Stmt::Error(_) | Stmt::Count(_) => {}
            Stmt::Branches(bs) => bs.iter_mut().for_each(f),
            Stmt::Guard { then: b, .. } | Stmt::Let { body: b, .. } | Stmt::ForEach { body: b, .. } | Stmt::Assign { body: b, .. } => f(b),
            Stmt::Compose { first, second, paths, .. } => {
                f(first);
                f(second);
                for path in paths {
                    f(&mut path.rest);
                }
            }
            Stmt::Repeat { body, rest, .. } => {
                f(body);
                f(rest);
            }
        }
    }

    pub fn has_composition(&self) -> bool {
        let mut found = matches!(self, Stmt::Compose { .. }) || self.expr().is_some_and(Expr::has_composition);
        self.for_each_sub_stmt(&mut |s| found |= s.has_composition());
        found
    }

    /// Distinct assignment masks at emits, in traversal order. None means
    /// an invalid variable/mask; the verifier checks this before execution.
    pub fn emitted_assignments(&self, nvars: usize) -> Option<Vec<Vec<bool>>> {
        fn walk(s: &Stmt, mask: &mut [bool], out: &mut Vec<Vec<bool>>) -> bool {
            match s {
                Stmt::Emit => {
                    if !out.iter().any(|previous| previous == mask) {
                        out.push(mask.to_vec());
                    }
                    true
                }
                Stmt::Assign { var, body, .. } => {
                    let Some(slot) = mask.get_mut(*var as usize) else { return false };
                    let old = std::mem::replace(slot, true);
                    let ok = walk(body, mask, out);
                    mask[*var as usize] = old;
                    ok
                }
                Stmt::Compose { paths, .. } => {
                    let old = mask.to_vec();
                    for path in paths {
                        if path.assigned.len() != mask.len() {
                            return false;
                        }
                        for (a, b) in mask.iter_mut().zip(&path.assigned) {
                            *a |= *b;
                        }
                        if !walk(&path.rest, mask, out) {
                            return false;
                        }
                        mask.copy_from_slice(&old);
                    }
                    true
                }
                _ => {
                    let mut ok = true;
                    s.for_each_sub_stmt(&mut |b| ok &= walk(b, mask, out));
                    ok
                }
            }
        }
        let mut out = Vec::new();
        walk(self, &mut vec![false; nvars], &mut out).then_some(out)
    }

    /// Call `f` on every direct sub-statement (in order).
    pub fn for_each_sub_stmt(&self, f: &mut dyn FnMut(&Stmt)) {
        match self {
            Stmt::Stop | Stmt::Emit | Stmt::Error(_) | Stmt::Count(_) => {}
            Stmt::Branches(bs) => bs.iter().for_each(f),
            Stmt::Guard { then: b, .. } | Stmt::Let { body: b, .. } | Stmt::ForEach { body: b, .. } | Stmt::Assign { body: b, .. } => f(b),
            Stmt::Compose { first, second, paths, .. } => {
                f(first);
                f(second);
                for path in paths {
                    f(&path.rest);
                }
            }
            Stmt::Repeat { body, rest, .. } => {
                f(body);
                f(rest);
            }
        }
    }
}

#[cfg(test)]
mod helper_tests {
    use super::*;

    fn flag(value: bool) -> Expr {
        Expr::new(Ty::Bool, ExprKind::Const(Value::Bool(value)))
    }

    fn interp(binding: Expr) -> Expr {
        Expr::new(
            Ty::Val,
            ExprKind::Interp {
                expr: hir::Expr::new(hir::ExprKind::Bool(false), hir::Span::default()),
                binds: vec![(hir::LocalId(0), binding)],
                deferred: vec![],
                env: Env::default(),
            },
        )
    }

    #[test]
    fn enabled_query_follows_nested_expressions_and_interp_bindings() {
        let enabled = Expr::new(Ty::Bool, ExprKind::Enabled(Box::new(Stmt::Emit)));
        assert!(enabled.contains_enabled());
        for leaf in [enabled, flag(false)] {
            let expected = leaf.contains_enabled();
            let nested = Expr::new(Ty::Bool, ExprKind::And(vec![flag(true), interp(Expr::new(Ty::Bool, ExprKind::Not(leaf)))]));
            assert_eq!(nested.contains_enabled(), expected);
        }
    }

    fn composition() -> Stmt {
        let guard = |id| Stmt::Guard { cond: Expr::new(Ty::Bool, ExprKind::Temp(id)), then: Box::new(Stmt::Emit) };
        Stmt::Compose {
            first: Box::new(guard(0)),
            second: Box::new(guard(1)),
            paths: vec![ComposePath { assigned: vec![], rest: guard(2) }, ComposePath { assigned: vec![], rest: guard(3) }],
            count: false,
        }
    }

    #[test]
    fn enabled_children_keep_all_compose_statements_in_order() {
        let mut enabled = Expr::new(Ty::Bool, ExprKind::Enabled(Box::new(composition())));
        let children = |expr: &Expr| {
            let mut ids = Vec::new();
            expr.for_each_child(&mut |child| {
                let ExprKind::Temp(id) = *child.kind else { panic!("temp sentinel") };
                ids.push(id);
            });
            ids
        };
        assert_eq!(children(&enabled), [0, 1, 2, 3]);
        enabled.for_each_child_mut(&mut |child| {
            let ExprKind::Temp(id) = &mut *child.kind else { panic!("temp sentinel") };
            *id += 10;
        });
        assert_eq!(children(&enabled), [10, 11, 12, 13]);
    }

    #[test]
    fn nested_enabled_is_visited_inside_each_compose_child() {
        for selected in 0..4 {
            let mut stmt = composition();
            stmt.for_each_expr_deep_mut(&mut |expr| {
                if matches!(*expr.kind, ExprKind::Temp(id) if id == selected) {
                    *expr = interp(Expr::new(Ty::Bool, ExprKind::Enabled(Box::new(Stmt::Emit))));
                }
            });
            let mut found = Vec::new();
            stmt.for_each_expr_deep(&mut |expr| found.push(expr.contains_enabled()));
            assert_eq!(found, (0..4).map(|id| id == selected).collect::<Vec<_>>());
        }
    }
}
