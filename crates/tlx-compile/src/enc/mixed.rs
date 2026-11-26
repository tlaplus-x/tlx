//! Host regions of mixed-mode native code (docs/mixed-mode.md §5): the
//! boxed IR subtrees generated C hands back to the host through
//! `host->eval`, evaluated by the IR executor on the call's states.
//!
//! `RegionTable` lists the regions of a library (expression, inputs,
//! call-site context, assigned next-state variables, and what the lowering
//! knows about them: purity, read set); the code generator that splits
//! functions into C and regions produces it, from the regions the lowering
//! shaped (`Lowerer::action_regions` / `pred_regions`).
//! `HostRegions` implements `tlx_native::mixed::Regions` over it, with
//! the closure-compiled executor (`exec::fast`).

use std::cell::RefCell;
use std::hash::Hasher;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, OnceLock};

use tlx_base::hash::StableHasher;
use tlx_eval::Interp;
use tlx_native::mixed::{Args, In, Kind, Out, RegionEnv, RegionError, RegionSig, Regions};
use tlx_runtime::stats;
use tlx_value::Value;

use crate::exec::{fast, memo, S1View};
use crate::ir::{Expr, IndexMap, ShapeId, Stmt, Temp, Ty};
use crate::types::Typing;

/// Where a region is called from: which states it sees.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RegionCtx {
    /// Init: no current state; the next state being built (`s1`).
    Init,
    /// An action: the current state and the next state being built.
    Action,
    /// A state predicate (invariant, constraint): the current state only.
    StatePred,
    /// A transition predicate (action property): both states, all of the
    /// next state assigned.
    TransPred,
}

/// One region: an IR expression evaluated by the host.
#[derive(Clone, Debug)]
pub struct Region {
    pub expr: Expr,
    /// Temps of the enclosing function (the executor's frame).
    pub temps: Arc<[Ty]>,
    /// The temps read by `expr` that the caller passes, in `args` order.
    pub inputs: Vec<Temp>,
    pub ctx: RegionCtx,
    /// Next-state variables statically assigned at the call site (Init and
    /// Action; `RegionTable::new` sets all for TransPred, none for
    /// StatePred).
    pub assigned: Arc<[bool]>,
    /// What the lowering knows about the region (default: nothing).
    pub info: RegionInfo,
}

/// Facts about a region from the lowering (docs/mixed-mode.md §4).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct RegionInfo {
    /// The function it belongs to.
    pub func: Arc<str>,
    /// Inside `ENABLED` (its next state is local to the `ENABLED`).
    pub enabled: bool,
    /// Free of side-effecting and nondeterministic builtins (R4); only
    /// pure regions may be memoized or evaluated speculatively.
    pub pure: bool,
    /// State variables it reads (None: unknown).
    pub reads: Option<Reads>,
}

/// State variables read by a region (sorted).
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct Reads {
    /// Of the current state.
    pub cur: Vec<u32>,
    /// Of the next state.
    pub next: Vec<u32>,
}

impl Region {
    /// The next-state variables the region may read as values (None:
    /// unknown). In Init, variables read the state being built.
    pub fn s1_reads(&self) -> Option<Vec<u32>> {
        let r = self.info.reads.as_ref()?;
        let mut v = r.next.clone();
        if self.ctx == RegionCtx::Init {
            v.extend(&r.cur);
            v.sort_unstable();
            v.dedup();
        }
        Some(v)
    }
}

/// The regions of one generated library, indexed by region id.
pub struct RegionTable {
    pub(crate) regions: Vec<Region>,
    sigs: Vec<RegionSig>,
    /// Per region: `Region::s1_reads`.
    s1_reads: Vec<Option<Vec<u32>>>,
    /// The FNV-1a hash of the table's structure, and its `StableHasher`
    /// hash (a second, independent hash for the build cache key).
    hash: u64,
    second: u64,
    /// For `canonical()`.
    shapes: Vec<String>,
    /// Per region: its results may be memoized (pure, known read set).
    memo_ok: Vec<bool>,
    /// Per region: the region whose memo node it shares (equivalent
    /// regions share one, `region_eq`; computed on first use, as it needs
    /// the interpreter's program).
    memo_class: OnceLock<Vec<u32>>,
    /// Per region: evaluations, failed ones and nanoseconds spent (counted
    /// with `-stats`, by the thread in `TALLY` and added here after each
    /// native call).
    counts: Arc<[[AtomicU64; 6]]>,
}

/// The evaluations of the calling thread's current native call, per region
/// (`-stats`): thread-local, so counting takes no atomic operation.
#[derive(Default)]
struct Tally {
    /// Per region id: evaluations, failed ones and nanoseconds spent.
    counts: Vec<[u64; 6]>,
    /// The regions with a nonzero count.
    touched: Vec<u32>,
}

thread_local! {
    static TALLY: RefCell<Tally> = RefCell::new(Tally::default());
}

impl RegionTable {
    pub fn new(typing: &Typing, mut regions: Vec<Region>) -> RegionTable {
        let nvars = typing.layout.vars.len();
        let (all, none): (Arc<[bool]>, Arc<[bool]>) = (vec![true; nvars].into(), Arc::from([]));
        for r in &mut regions {
            match r.ctx {
                RegionCtx::TransPred => r.assigned = all.clone(),
                RegionCtx::StatePred => r.assigned = none.clone(),
                RegionCtx::Init | RegionCtx::Action => assert_eq!(r.assigned.len(), nvars, "assigned variables of an Init/Action region"),
            }
        }
        for r in &regions {
            crate::verify::region(typing, r).expect("invalid host region IR");
        }
        let kind = |t: Ty| match t {
            Ty::Bool | Ty::Int => Kind::Scalar,
            Ty::Enc(sid) => Kind::Words(typing.words(sid)),
            Ty::Val => Kind::Handle,
        };
        let sigs: Vec<RegionSig> = regions
            .iter()
            .map(|r| RegionSig { inputs: r.inputs.iter().map(|t| kind(r.temps[*t as usize])).collect(), result: kind(r.expr.ty) })
            .collect();
        let shapes = (0..typing.num_shapes() as ShapeId).map(|sid| format!("{:?}", typing.shape(sid))).collect();
        let s1_reads = regions.iter().map(Region::s1_reads).collect();
        let memo_ok = regions.iter().map(|r| r.info.pure && r.info.reads.is_some()).collect();
        let counts = regions.iter().map(|_| std::array::from_fn(|_| AtomicU64::new(0))).collect();
        let mut t = RegionTable { regions, sigs, s1_reads, hash: 0, second: 0, shapes, memo_ok, memo_class: OnceLock::new(), counts };
        let mut h = Hashing { fnv: FNV_BASIS, second: StableHasher::new(), consts: Default::default() };
        t.hash_structure(&mut h);
        (t.hash, t.second) = (h.fnv, h.second.finish());
        t
    }

    /// Verified region descriptions, immutable after the ABI table is built.
    pub fn regions(&self) -> &[Region] {
        &self.regions
    }

    /// A deterministic description of the table (for debugging; it can be
    /// hundreds of MB: it prints the HIR of interpreter fallbacks).
    pub fn canonical(&self) -> String {
        let mut out = String::new();
        self.write_canonical(&mut out).expect("writing to a string does not fail");
        out
    }

    pub fn hash(&self) -> u64 {
        self.hash
    }

    /// Two independent 64-bit hashes of the table's structure (FNV-1a,
    /// `StableHasher`; both stable across toolchains): the code generator writes them into the C source, so that
    /// the build cache key covers the regions.
    pub fn digest(&self) -> String {
        format!("{:016x}{:016x}", self.hash, self.second)
    }

    #[cfg(feature = "jit")]
    pub(crate) fn verify_typing(&self, typing: &Typing) -> Result<(), String> {
        if self.shapes.len() != typing.num_shapes()
            || self.shapes.iter().enumerate().any(|(i, s)| *s != format!("{:?}", typing.shape(i as ShapeId)))
        {
            return Err("region table belongs to a different shape registry".into());
        }
        for r in &self.regions {
            crate::verify::region(typing, r)?;
        }
        Ok(())
    }

    /// Add the evaluations the calling thread counted since the last call
    /// to the table's counts; returns their number and how many failed.
    pub fn drain_counts(&self) -> (u64, u64) {
        TALLY.with(|t| {
            let t = &mut *t.borrow_mut();
            let mut total = (0, 0);
            for rid in t.touched.drain(..) {
                let counts = std::mem::take(&mut t.counts[rid as usize]);
                let [evals, errors, ..] = counts;
                for (dst, value) in self.counts[rid as usize].iter().zip(counts) {
                    dst.fetch_add(value, Ordering::Relaxed);
                }
                total = (total.0 + evals, total.1 + errors);
            }
            total
        })
    }

    /// Per region, the region whose memo node it uses (`region_eq`).
    pub fn memo_class(&self, prog: &tlx_sema::Program) -> &[u32] {
        self.memo_class.get_or_init(|| super::region_eq::memo_classes(&self.regions, &self.memo_ok, &self.s1_reads, prog))
    }

    /// Every evaluated region (counted with `-stats`, memo hits
    /// included), most time first: one line each with its time,
    /// evaluations, failures, function, root and the state variables it
    /// reads (`vars` names them).
    pub fn report(&self, vars: &[&str]) -> String {
        let count = |r: usize, i: usize| self.counts[r][i].load(Ordering::Relaxed);
        let mut rids: Vec<usize> = (0..self.regions.len()).filter(|&r| count(r, 0) > 0).collect();
        rids.sort_by_key(|&r| (std::cmp::Reverse(count(r, 2)), std::cmp::Reverse(count(r, 0))));
        let mut out = String::new();
        for &rid in rids.iter() {
            let r = &self.regions[rid];
            let (evals, errors, secs) = (count(rid, 0), count(rid, 1), count(rid, 2) as f64 / 1e9);
            let mut root = crate::coverage::region_root(&r.expr);
            if root.chars().count() > 90 {
                root = root.chars().take(89).collect::<String>() + "~";
            }
            let memo = match self.memo_class.get().map(|c| c[rid] as usize) {
                _ if !self.memo_ok[rid] => ", not memoizable".to_string(),
                Some(q) if q != rid => format!(", memo of region {q}"),
                _ => String::new(),
            };
            let reads = match &r.info.reads {
                Some(rd) => {
                    let name = |v: &u32| vars.get(*v as usize).copied().unwrap_or("?");
                    let mut names: Vec<String> = rd.cur.iter().map(|v| name(v).to_string()).collect();
                    names.extend(rd.next.iter().map(|v| format!("{}'", name(v))));
                    if names.is_empty() {
                        String::new()
                    } else {
                        format!(" [reads {}]", names.join(", "))
                    }
                }
                None => " [reads unknown]".to_string(),
            };
            out += &format!(
                "  region {rid:<6} {secs:>8.3}s {evals:>12} evals {errors:>9} failed  {:?} in {}{memo}: {root}{reads}\n",
                r.ctx, r.info.func
            );
        }
        out
    }

    /// Prepare immutable census metadata once and retain only the atomic
    /// counters. The callback does not retain the model, IR or native libraries,
    /// and serialization never runs inside a sampled native evaluation.
    pub fn json_source(&self, typing: &Typing) -> impl Fn() -> String + Send + Sync + 'static {
        let prefixes: Vec<_> = self
            .regions
            .iter()
            .enumerate()
            .map(|(rid, r)| {
                let mut root = &r.expr;
                loop {
                    match &*root.kind {
                        crate::ir::ExprKind::Convert(x) => root = x,
                        crate::ir::ExprKind::Let { body, .. } => root = body,
                        _ => break,
                    }
                }
                let (operation, arguments) = crate::coverage::operation(root, typing);
                let args = arguments.iter().map(|a| stats::json_string(a)).collect::<Vec<_>>().join(",");
                format!(
                    "{{\"id\":{rid},\"function\":{},\"context\":{},\"operation\":{},\"arguments\":[{args}]",
                    stats::json_string(&r.info.func),
                    stats::json_string(&format!("{:?}", r.ctx)),
                    stats::json_string(&operation)
                )
            })
            .collect();
        let counts = self.counts.clone();
        move || {
            let rows: Vec<_> = prefixes
                .iter()
                .zip(counts.iter())
                .map(|(prefix, counts)| {
                    format!(
                        "{prefix},\"calls\":{},\"errors\":{},\"time_s\":{:.9}}}",
                        counts[3].load(Ordering::Relaxed),
                        counts[4].load(Ordering::Relaxed),
                        counts[5].load(Ordering::Relaxed) as f64 / 1e9
                    )
                })
                .collect();
            format!("[{}]", rows.join(","))
        }
    }

    /// Region evaluations and time per state variable they read (current
    /// or next state; a region reading several variables counts for each,
    /// one with unknown reads under `?`; a region whose inputs are only
    /// temporaries reads no state variable), most evaluations first.
    pub fn report_by_var(&self, vars: &[&str]) -> String {
        let count = |r: usize, i: usize| self.counts[r][i].load(Ordering::Relaxed);
        let mut per: std::collections::BTreeMap<String, (u64, u64, u64)> = Default::default();
        let (mut evals, mut nanos) = (0, 0);
        for rid in (0..self.regions.len()).filter(|&r| count(r, 0) > 0) {
            let (e, n) = (count(rid, 0), count(rid, 2));
            evals += e;
            nanos += n;
            let names: Vec<&str> = match &self.regions[rid].info.reads {
                Some(rd) => {
                    let mut vs: Vec<u32> = rd.cur.iter().chain(rd.next.iter()).copied().collect();
                    vs.sort_unstable();
                    vs.dedup();
                    if vs.is_empty() {
                        vec!["(no state variable)"]
                    } else {
                        vs.iter().map(|v| vars.get(*v as usize).copied().unwrap_or("?")).collect()
                    }
                }
                None => vec!["?"],
            };
            for name in names {
                let row = per.entry(name.to_string()).or_default();
                row.0 += e;
                row.1 += n;
                row.2 += 1;
            }
        }
        if evals == 0 {
            return String::new();
        }
        let mut rows: Vec<(String, (u64, u64, u64))> = per.into_iter().collect();
        rows.sort_by_key(|(name, (e, ..))| (std::cmp::Reverse(*e), name.clone()));
        let mut out = format!("  all regions                {evals:>12} evals {:>8.3}s\n", nanos as f64 / 1e9);
        for (name, (e, n, k)) in rows {
            out += &format!("  reading {name:<18} {e:>12} evals {:>8.3}s  ({k} regions)\n", n as f64 / 1e9);
        }
        out
    }

    pub fn len(&self) -> usize {
        self.regions.len()
    }

    /// How region `rid`'s inputs and result cross the ABI.
    pub fn sig(&self, rid: u32) -> &RegionSig {
        &self.sigs[rid as usize]
    }

    pub fn is_empty(&self) -> bool {
        self.regions.is_empty()
    }
}

impl RegionTable {
    /// Text of a type, with the shape of an encoding (shape ids are only
    /// meaningful within one typing).
    fn ty_text(&self, t: Ty) -> String {
        match t {
            Ty::Enc(sid) => format!("Enc({})", self.shapes[sid as usize]),
            t => format!("{t:?}"),
        }
    }

    fn write_canonical(&self, out: &mut dyn std::fmt::Write) -> std::fmt::Result {
        for (rid, r) in self.regions.iter().enumerate() {
            self.write_region(out, rid, r)?;
        }
        Ok(())
    }

    fn write_region(&self, out: &mut dyn std::fmt::Write, rid: usize, r: &Region) -> std::fmt::Result {
        let temps: Vec<String> = r.temps.iter().map(|t| self.ty_text(*t)).collect();
        let assigned: String = r.assigned.iter().map(|a| if *a { '1' } else { '0' }).collect();
        let i = &r.info;
        let reads = match &i.reads {
            None => "?".to_string(),
            Some(rd) => format!("{:?}/{:?}", rd.cur, rd.next),
        };
        writeln!(
            out,
            "region {rid} {:?}{} result {} inputs {:?} assigned {assigned} temps [{}] in {:?} {} reads {reads}\n  {:?}",
            r.ctx,
            if i.enabled { " enabled" } else { "" },
            self.ty_text(r.expr.ty),
            r.inputs,
            temps.join(", "),
            i.func,
            if i.pure { "pure" } else { "impure" },
            r.expr
        )
    }
}

impl RegionTable {
    /// Feed the table's structure to `h` (the library's `regions_hash`):
    /// per region its signature, context, assigned variables, facts and
    /// expression tree. Interpreter fallbacks are identified by their
    /// source positions and captures, not by their HIR (hashing
    /// their printed form took seconds on large specs). What the generated
    /// code relies on (region ids, inputs, result representations) is in
    /// the C source itself; the hash guards against loading a library with
    /// another table.
    fn hash_structure(&self, h: &mut Hashing) {
        h.u64(self.shapes.len() as u64);
        for s in &self.shapes {
            h.str(s);
        }
        h.u64(self.regions.len() as u64);
        for r in &self.regions {
            h.u64(r.temps.len() as u64);
            for t in r.temps.iter() {
                hash_ty(h, *t);
            }
            h.u64(r.inputs.len() as u64);
            for t in &r.inputs {
                h.u64(*t as u64);
            }
            h.u64(r.ctx as u64);
            h.u64(r.assigned.len() as u64);
            for a in r.assigned.iter() {
                h.u64(*a as u64);
            }
            let i = &r.info;
            h.str(&i.func);
            h.u64(i.enabled as u64 | (i.pure as u64) << 1);
            match &i.reads {
                None => h.u64(u64::MAX),
                Some(rd) => {
                    for v in [&rd.cur, &rd.next] {
                        h.u64(v.len() as u64);
                        v.iter().for_each(|x| h.u64(*x as u64));
                    }
                }
            }
            hash_expr(h, &r.expr);
        }
    }
}

fn hash_ty(h: &mut Hashing, t: Ty) {
    match t {
        Ty::Bool => h.u64(1),
        Ty::Int => h.u64(2),
        Ty::Enc(sid) => h.u64(3 | (sid as u64) << 8),
        Ty::Val => h.u64(4),
    }
}

/// Feed the structure of `e` to `h`: per node its kind, type and every
/// payload that is not a child expression (indices, offsets, sizes,
/// tables, constants, operators, flags, the number of children of a
/// variadic node; for an interpreter fallback the source span of its
/// expression and its captures; for `ENABLED` its statement tree), then
/// its children. The match is exhaustive (no `_` arm), so a new kind does
/// not compile until its payload is hashed here.
fn hash_expr(h: &mut Hashing, e: &Expr) {
    use crate::ir::{Deferred, ExprKind as K};
    // (The variant's index, through `Hashing`'s `Hasher`.)
    std::hash::Hash::hash(&std::mem::discriminant(&*e.kind), h);
    hash_ty(h, e.ty);
    let span = |h: &mut Hashing, x: &tlx_sema::hir::Expr| {
        h.u64(x.span.file.0 as u64);
        h.u64((x.span.start as u64) << 32 | x.span.end as u64);
    };
    let words = |h: &mut Hashing, w: &[u64]| {
        h.u64(w.len() as u64);
        w.iter().for_each(|x| h.u64(*x));
    };
    let table = |h: &mut Hashing, t: &[i32]| {
        h.u64(t.len() as u64);
        t.iter().for_each(|x| h.u64(*x as i64 as u64));
    };
    let loc = |h: &mut Hashing, l: crate::ir::FieldLoc| match l {
        crate::ir::FieldLoc::Words(w) => {
            h.u64(0);
            h.u64(w as u64);
        }
        crate::ir::FieldLoc::Bits(p) => {
            h.u64(1);
            h.u64((p.word as u64) << 16 | (p.shift as u64) << 8 | p.bits as u64);
        }
    };
    let slot = |h: &mut Hashing, s: crate::ir::SlotLayout| match s {
        crate::ir::SlotLayout::Words(w) => {
            h.u64(0);
            h.u64(w as u64);
        }
        crate::ir::SlotLayout::Bits(b) => {
            h.u64(1);
            h.u64(b as u64);
        }
    };
    match &*e.kind {
        K::Const(v) => h.value(v),
        K::ConstWords(w) => words(h, w),
        K::OrderedSet { plan, .. } => words(h, plan),
        K::Var(v) | K::NextVar(v) => h.u64(*v as u64),
        K::Temp(t) => h.u64(*t as u64),
        K::Not(_)
        | K::If(..)
        | K::Neg(_)
        | K::Eq(..)
        | K::Convert(_)
        | K::Apply(..)
        | K::BitMember { .. }
        | K::BitCard(_)
        | K::Rank(_)
        | K::SeqLen(_)
        | K::IntRange(..)
        | K::Subsets(_)
        | K::MapGet { .. }
        | K::MapMerge(..) => {}
        K::And(xs) | K::Or(xs) | K::Concat(xs) | K::BitSet(xs) | K::Tuple(xs) => h.u64(xs.len() as u64),
        K::Pack { locs, parts } => {
            h.u64(parts.len() as u64);
            locs.iter().for_each(|l| loc(h, *l));
        }
        K::IntBin(op, ..) => h.str(&format!("{op:?}")),
        K::IntCmp(op, ..) => h.str(&format!("{op:?}")),
        K::BitSetOp(op, ..) => h.str(&format!("{op:?}")),
        K::Exists { bind, .. }
        | K::Forall { bind, .. }
        | K::Choose { bind, .. }
        | K::Filter { bind, .. }
        | K::Collect { bind, .. }
        | K::UnionFold { bind, .. } => h.u64(*bind as u64),
        K::MapBuild { bind, witness, .. } => {
            h.u64(*bind as u64);
            h.u64(witness.map_or(u64::MAX, |w| w));
        }
        K::MapSet { bind, cond, .. } => h.u64((*bind as u64) << 1 | cond.is_some() as u64),
        K::Fold { product, bind, .. } => h.u64((*bind as u64) << 1 | *product as u64),
        K::Let { temp, .. } => h.u64(*temp as u64),
        K::ValField(_, f) => h.str(&format!("{f:?}")),
        K::RefOp { op, args } => {
            h.str(&format!("{op:?}"));
            h.u64(args.len() as u64);
        }
        K::RefElems(_) => h.str("refelems"),
        K::Slice { loc: l, .. } | K::ExceptAt { loc: l, .. } => loc(h, *l),
        K::Index { map, slot: s, .. } | K::ExceptIndex { map, slot: s, .. } => {
            slot(h, *s);
            match map {
                IndexMap::IntRange { lo, n } => {
                    h.u64(0);
                    h.u64(*lo as u64);
                    h.u64(*n as u64);
                }
                IndexMap::Table(t) => {
                    h.u64(1);
                    table(h, t);
                }
            }
        }
        K::SeqIndex { slot: s, .. } | K::SeqTail { slot: s, .. } | K::SeqSub { slot: s, .. } => slot(h, *s),
        K::SortedMember { elem_words, .. } => h.u64(*elem_words as u64),
        K::SeqAppend { slot: s, max_len: max, .. } | K::SeqConcat { slot: s, max_len: max, .. } => {
            slot(h, *s);
            h.u64(*max as u64);
        }
        K::SortedInsert { elem_words, max_card: max, .. } => h.u64((*elem_words as u64) << 32 | *max as u64),
        K::SortedOp { op, elem_words, max_card, .. } => {
            h.str(&format!("{op:?}"));
            h.u64((*elem_words as u64) << 32 | *max_card as u64);
        }
        K::SeqFilter { bind, slot: s, .. } => {
            h.u64(*bind as u64);
            slot(h, *s);
        }
        K::UnionField { locs, .. } => {
            h.u64(locs.len() as u64);
            for o in locs.iter() {
                match o {
                    None => h.u64(u64::MAX),
                    Some(l) => loc(h, *l),
                }
            }
        }
        K::UnionFieldInt { entries, .. } => {
            h.u64(entries.len() as u64);
            for x in entries.iter() {
                match x {
                    None => h.u64(u64::MAX),
                    Some((l, lo)) => {
                        loc(h, *l);
                        h.u64(*lo as u64);
                    }
                }
            }
        }
        K::ConstElems { elem, words: w, count } => {
            h.u64((*elem as u64) << 32 | *count as u64);
            words(h, w);
        }
        K::Fail(m) => h.str(m),
        K::RankFlat { radices, .. } => words(h, radices),
        K::Recode { arm_base, table: t, words: n, .. } => {
            words(h, arm_base);
            words(h, t);
            h.u64(*n as u64);
        }
        K::RankUnion { arms, .. } => {
            h.u64(arms.len() as u64);
            arms.iter().for_each(|a| words(h, a));
        }
        K::Lookup { table: t, .. } => table(h, t),
        // (The plan's rejected ranks follow from the node's type; insert_witness varies per site.)
        K::MapPut { plan, .. } => {
            h.u64(plan.inserts() as u64);
            h.u64(plan.insert_witness.map_or(u64::MAX, |w| w));
        }
        // Its statement tree, instead of the expressions in it.
        K::Enabled(s) => return hash_stmt(h, s),
        K::Call { func, args } => {
            h.u64(*func as u64);
            h.u64(args.len() as u64);
        }
        K::ValOp { op, args } => {
            h.str(op.name());
            h.u64(args.len() as u64);
        }
        // `env` (the constant bindings of the fallback's context) is left
        // out: only the host reads it, when it evaluates a region of its
        // own table (the generated code never sees it), and hashing it
        // would mean hashing values and HIR.
        K::Interp { expr, binds, deferred, env: _ } => {
            span(h, expr);
            h.u64(binds.len() as u64);
            for (l, _) in binds {
                h.u64(l.0 as u64);
            }
            h.u64(deferred.len() as u64);
            for x in deferred {
                std::hash::Hash::hash(&std::mem::discriminant(x), h);
                match x {
                    Deferred::Thunk(l, x) | Deferred::Once(l, x) => {
                        h.u64(l.0 as u64);
                        span(h, x);
                    }
                    Deferred::Lambda(l, params, x) => {
                        h.u64(l.0 as u64);
                        h.u64(params.len() as u64);
                        params.iter().for_each(|p| h.u64(p.0 as u64));
                        span(h, x);
                    }
                    Deferred::OpRef(l, r) => {
                        h.u64(l.0 as u64);
                        h.str(&format!("{r:?}"));
                    }
                }
            }
        }
    }
    e.for_each_child(&mut |c| hash_expr(h, c));
}

/// Feed the structure of the statement tree `s` (of an `ENABLED`) to `h`:
/// per statement its kind and payload, then its expression and its
/// sub-statements.
fn hash_stmt(h: &mut Hashing, s: &Stmt) {
    std::hash::Hash::hash(&std::mem::discriminant(s), h);
    match s {
        Stmt::Stop | Stmt::Emit | Stmt::Guard { .. } | Stmt::If { .. } => {}
        Stmt::Then { assigned, .. } => {
            h.u64(assigned.len() as u64);
            for a in assigned {
                h.u64(*a as u64);
            }
        }
        Stmt::Branches(bs) => h.u64(bs.len() as u64),
        Stmt::Let { temp, .. } => h.u64(*temp as u64),
        Stmt::ForEach { bind, iter, .. } => h.u64((*bind as u64) << 2 | *iter as u64),
        Stmt::Assign { var, .. } => h.u64(*var as u64),
        Stmt::Error(m) => h.str(m),
        Stmt::Repeat { id, bind, .. } => h.u64((*id as u64) << 32 | *bind as u64),
        Stmt::Count(id) => h.u64(*id as u64),
        Stmt::Compose { paths, count, .. } => {
            h.u64(*count as u64);
            h.u64(paths.len() as u64);
            for path in paths {
                for a in &path.assigned {
                    h.u64(*a as u64);
                }
            }
        }
    }
    if let Some(e) = s.expr() {
        hash_expr(h, e);
    }
    s.for_each_sub_stmt(&mut |b| hash_stmt(h, b));
}

const FNV_BASIS: u64 = 0xcbf29ce484222325;

/// Two hashes (FNV-1a and `StableHasher`) of what is fed to it. (Also a
/// `Hasher`, with integers fed little-endian, for values that only offer
/// `Hash`.)
struct Hashing {
    fnv: u64,
    second: StableHasher,
    /// The digests of the constants hashed so far, by the address of their
    /// shared elements (a trace validation's log is one value that
    /// hundreds of regions refer to).
    consts: tlx_base::hash::FxMap<usize, u64>,
}

impl std::hash::Hasher for Hashing {
    fn write(&mut self, b: &[u8]) {
        self.bytes(b);
    }
    fn write_u64(&mut self, x: u64) {
        self.u64(x);
    }
    fn write_isize(&mut self, x: isize) {
        self.u64(x as i64 as u64);
    }
    fn write_usize(&mut self, x: usize) {
        self.u64(x as u64);
    }
    fn finish(&self) -> u64 {
        unreachable!("Hashing is read through its fields")
    }
}

impl Hashing {
    fn bytes(&mut self, b: &[u8]) {
        self.fnv = b.iter().fold(self.fnv, |h, x| (h ^ *x as u64).wrapping_mul(0x100000001b3));
        self.second.write(b);
    }

    fn u64(&mut self, x: u64) {
        self.bytes(&x.to_le_bytes());
    }

    /// A string, length first (so that consecutive strings stay apart).
    fn str(&mut self, s: &str) {
        self.u64(s.len() as u64);
        self.bytes(s.as_bytes());
    }

    /// A constant: its kind and size, and a digest of its contents (its
    /// fingerprint, which equal values share; its printed form if it has
    /// none), computed once per shared value.
    fn value(&mut self, v: &Value) {
        let shared = match v {
            Value::Set(a) | Value::Tuple(a) => Some((Arc::as_ptr(a) as *const () as usize, a.len())),
            Value::Record(a) => Some((Arc::as_ptr(a) as *const () as usize, a.len())),
            Value::Fcn(a, dom) => {
                self.str(&format!("{dom:?}"));
                Some((Arc::as_ptr(a) as *const () as usize, a.len()))
            }
            _ => None,
        };
        let Some((at, len)) = shared else { return self.str(&format!("{v:?}")) };
        std::hash::Hash::hash(&std::mem::discriminant(v), self);
        self.u64(len as u64);
        let digest = match self.consts.get(&at) {
            Some(&d) => d,
            None => {
                let d = tlx_value::fingerprint::fingerprint(v).unwrap_or_else(|_| {
                    let mut h = StableHasher::new();
                    std::hash::Hasher::write(&mut h, format!("{v:?}").as_bytes());
                    std::hash::Hasher::finish(&h)
                });
                self.consts.insert(at, d);
                d
            }
        };
        self.u64(digest);
    }
}

/// The evaluator of a model's regions (cheap to make per call).
pub struct HostRegions<'a> {
    pub ip: &'a Arc<Interp>,
    pub typing: &'a Typing,
    pub table: &'a RegionTable,
    /// Memo scope of the regions' results (0: not memoized).
    pub memo: u64,
    /// The closure-compiled executor (None: the native call bails out).
    pub fast: Option<FastRegions<'a>>,
}

/// The regions of a table compiled for the closure executor (`exec::fast`):
/// all compiled ahead by `FastRegions::compile`, or each one compiled on its
/// first use in a slot from `FastRegions::slots`.
#[derive(Clone, Copy)]
pub struct FastRegions<'a> {
    /// The compiled functions of the lowering the regions belong to.
    pub prog: &'a fast::Program,
    /// Per region (`FastRegions::slots`): its compiled expression, or None
    /// if it is not covered (the enclosing native call bails out).
    pub progs: &'a [OnceLock<Option<fast::ExprProg>>],
}

impl FastRegions<'_> {
    /// Compile the verified host regions before state exploration starts.
    /// A region that is not covered is cached as `None`; the cause is
    /// recovered at the diagnostic boundary (`HostRegions::eval_now`),
    /// which is the only place that reads it.
    pub(crate) fn compile(table: &RegionTable, typing: &Typing, prog: &fast::Program) -> Vec<OnceLock<Option<fast::ExprProg>>> {
        table.regions.iter().map(|r| OnceLock::from(prog.expr(typing, &r.temps, &r.inputs, &r.expr).ok())).collect()
    }

    /// Empty slots for the regions of `table`.
    pub fn slots(table: &RegionTable) -> Vec<OnceLock<Option<fast::ExprProg>>> {
        (0..table.len()).map(|_| OnceLock::new()).collect()
    }
}

impl Regions for HostRegions<'_> {
    fn len(&self) -> u32 {
        self.table.regions.len() as u32
    }

    fn hash(&self) -> u64 {
        self.table.hash
    }

    fn sig(&self, rid: u32) -> &RegionSig {
        &self.table.sigs[rid as usize]
    }

    fn eval(&self, rid: u32, args: &Args<'_>, env: &mut RegionEnv<'_>) -> Result<Out, RegionError> {
        let start = stats::on().then(std::time::Instant::now);
        let r =
            if self.memo != 0 && self.table.memo_ok[rid as usize] { self.eval_memo(rid, args, env) } else { self.eval_now(rid, args, env) };
        if let Some(start) = start {
            self.count(rid, r.is_err(), start.elapsed().as_nanos() as u64);
        }
        r
    }
}

impl HostRegions<'_> {
    /// Count an evaluation of region `rid` that took `nanos` (`-stats`).
    #[inline(never)]
    fn count(&self, rid: u32, failed: bool, nanos: u64) {
        let search = stats::in_search_unit();
        TALLY.with(|t| {
            let t = &mut *t.borrow_mut();
            if t.counts.len() < self.table.len() {
                t.counts.resize(self.table.len(), [0; 6]);
            }
            let c = &mut t.counts[rid as usize];
            if *c == [0; 6] {
                t.touched.push(rid);
            }
            c[0] += 1;
            c[1] += failed as u64;
            c[2] += nanos;
            if search {
                c[3] += 1;
                c[4] += failed as u64;
                c[5] += nanos;
            }
        });
    }

    /// Evaluate region `rid` in the IR executor.
    fn eval_now(&self, rid: u32, args: &Args<'_>, env: &mut RegionEnv<'_>) -> Result<Out, RegionError> {
        let r = &self.table.regions[rid as usize];
        let s0 = if r.ctx == RegionCtx::Init { None } else { Some(env.s0.expect("region called without the current state")) };
        let s1 = match r.ctx {
            RegionCtx::StatePred => None,
            _ => Some(S1View { words: env.s1.expect("region called without the next state"), assigned: &r.assigned[..] }),
        };
        // The current state is decoded (through the call's state cache)
        // only if the region reads it as values.
        let cache = RefCell::new(&mut *env.cache);
        let decode = |w: &[u64]| {
            // SAFETY: the matching encoder/program produced these words.
            // Active Dyn handles were published before this call.
            cache.borrow_mut().get(w, |w| unsafe { self.typing.layout.decode_state_unchecked(w) })
        };
        let s1_reads = self.table.s1_reads[rid as usize].as_deref();
        let compiled = self.fast.as_ref().ok_or_else(|| RegionError(format!("region {rid}: IR closure not available")))?;
        let expression = compiled.progs[rid as usize].get_or_init(|| compiled.prog.expr(self.typing, &r.temps, &r.inputs, &r.expr).ok());
        let Some(expression) = expression.as_ref() else {
            // A slot caches only that the region is not covered; recompile
            // it here, on the cold path (the native call bails out on the
            // first such region anyway), so the diagnostic names the cause
            // instead of a bare "not covered".
            let why = compiled.prog.expr(self.typing, &r.temps, &r.inputs, &r.expr).err().unwrap_or_else(|| "unknown".into());
            return Err(RegionError(format!("region {rid}: IR closure not covered: {why}")));
        };
        let run = fast::Run::words(self.ip, self.typing, compiled.prog, env.level).with_decoder(&decode);

        // SAFETY: valid words from the matching encoder/program, with published Dyn handles.
        unsafe { fast::eval_region(&run, expression, s0, s1, s1_reads, args) }.map_err(|error| RegionError(error.into_message()))
    }

    /// `eval_now`, memoized (docs/mixed-mode.md §8): the key is the
    /// region's inputs as C passes them (scalars, encoding words; a boxed
    /// input by its structural encoding) and the words of the state
    /// variables it reads. Only pure regions with a known read set
    /// (`RegionTable::memo_ok`); errors are not memoized. Equivalent
    /// regions (`region_eq`) share the memo node of the first of them.
    fn eval_memo(&self, rid: u32, args: &Args<'_>, env: &mut RegionEnv<'_>) -> Result<Out, RegionError> {
        let r = &self.table.regions[rid as usize];
        let class = self.table.memo_class(&self.ip.prog)[rid as usize];
        // Region results share the memo table with interpreted IR nodes,
        // which are keyed by their (heap) addresses: tagged ids do not
        // collide with those.
        let node = REGION_NODE | class as usize;
        let memo::Probe::On(_) = memo::probe(self.memo, node, || {
            (Some(memo::Deps { vars: Vec::new() }), format!("region {class} in {}", self.table.regions[class as usize].info.func))
        }) else {
            return self.eval_now(rid, args, env);
        };
        let mut key = memo::KeyBuf::new();
        let mut keyed = true;
        for i in 0..args.len() {
            match args.get(i) {
                In::Int(x) => key.words.push(x as u64),
                In::Words(w) => key.words.extend_from_slice(w),
                In::Val(v) => keyed &= memo::push_value(v, &mut key.words),
            }
        }
        let t = self.typing;
        if r.ctx != RegionCtx::Init {
            if let (Some(s0), Some(rd)) = (env.s0, &r.info.reads) {
                rd.cur.iter().for_each(|&v| key.words.extend_from_slice(&s0[t.var_range(v as usize)]));
            }
        }
        if let (Some(s1), Some(reads)) = (env.s1, &self.table.s1_reads[rid as usize]) {
            reads.iter().for_each(|&v| key.words.extend_from_slice(&s1[t.var_range(v as usize)]));
        }
        if !keyed {
            memo::unkeyed(node, key);
            return self.eval_now(rid, args, env);
        }
        if let Some(c) = memo::get_cached(node, &key) {
            memo::release(key);
            return Ok(match (r.expr.ty, c) {
                (Ty::Bool, memo::Cached::Val(Value::Bool(b))) => Out::Bool(b),
                (Ty::Int, memo::Cached::Val(Value::Int(i))) => Out::Int(i),
                (Ty::Val, memo::Cached::Val(v)) => Out::Val(v),
                (Ty::Enc(_), memo::Cached::Words(w)) => Out::Words(w),
                (ty, c) => panic!("region {rid}: memoized {c:?} for type {ty:?}"),
            });
        }
        let t0 = memo::probation_timer(node);
        let out = self.eval_now(rid, args, env);
        let cached = out.as_ref().ok().map(|o| match o {
            Out::Bool(b) => memo::Cached::Val(Value::Bool(*b)),
            Out::Int(i) => memo::Cached::Val(Value::Int(*i)),
            Out::Val(v) => memo::Cached::Val(v.clone()),
            Out::Words(w) => memo::Cached::Words(w.clone()),
        });
        memo::fill_cached(node, key, cached, t0);
        out
    }
}

/// Tag of the memo node ids of regions (see `HostRegions::eval_memo`).
const REGION_NODE: usize = 1 << (usize::BITS - 1);

#[cfg(test)]
#[path = "mixed_tests.rs"]
mod tests;
