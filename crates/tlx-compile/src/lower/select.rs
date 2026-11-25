//! Selecting parts of values: function application, record fields
//! (including unions of records), `EXCEPT`, and sequence operators on
//! encoded values. Projections of literals (`<<a, b>>[1]`, `[f |-> e].f`,
//! also behind definitions and by-name arguments) select the component
//! expression without building the literal.

use tlx_sema::builtins::Builtin as B;
use tlx_sema::hir::{self, ExprKind as H};
use tlx_value::{Sym, Value};

use super::*;

/// How an argument selects a slot of an encoded function/tuple/record.
#[derive(Clone)]
pub(super) enum Sel {
    /// A fixed word or bitfield location.
    Loc(FieldLoc),
    /// A computed slot (with homogeneous `SlotLayout`).
    Index(IndexMap, SlotLayout),
    /// A slot at a computed position (an unboxed integer, -1 = not in the
    /// domain) among `n` slots of homogeneous `SlotLayout`.
    Pos(Expr, u32, SlotLayout),
}

impl Lowerer<'_> {
    /// `r.field`.
    pub(super) fn typed_field(&mut self, record: &hir::Expr, field: &str, env: &LEnv, st: &St) -> Expr {
        if let Some((r, renv)) = self.peel_call(record, env) {
            if let H::Record(fs) = &*r.kind {
                if let Some(i) = fs.iter().position(|(n, _)| &**n == field) {
                    let es: Vec<&hir::Expr> = fs.iter().map(|(_, e)| e).collect();
                    if self.others_infallible(&es, i, &renv) {
                        return self.expr(es[i], &renv, st);
                    }
                }
            }
        }
        let r = self.expr(record, env, st);
        let sym = Sym::new(field);
        if self.is_ref(r.ty) {
            return self.ref_op(crate::ir::RefOp::Field(sym), vec![r]);
        }
        match self.shape_of(r.ty).cloned() {
            Some(Shape::Record(fields)) => {
                if let Some((loc, fs)) = self.field_slot(&fields, sym) {
                    let fsid = self.sid(&fs);
                    return Expr::new(Ty::Enc(fsid), ExprKind::Slice { base: r, loc });
                }
                return Expr::new(Ty::Val, ExprKind::Fail("Attempted to access a field that the record does not have.".into()));
            }
            // A record built as a function over an enumerated set of strings
            // (`[k \in {"a", "b"} |-> e]`): the slot of the key.
            Some(Shape::Fcn { dom, range }) => {
                if let Some(i) = dom.iter().position(|k| matches!(k, Value::Str(s) if *s == sym)) {
                    let loc = SlotLayout::of(&range).loc(0, i);
                    let fsid = self.sid(&range);
                    return Expr::new(Ty::Enc(fsid), ExprKind::Slice { base: r, loc });
                }
            }
            Some(Shape::Union(arms)) => {
                if let Some(x) = self.union_field(r.clone(), &arms, sym) {
                    return x;
                }
            }
            // A record built with `:>` and `@@` (a map over strings): the
            // slot of the key (absent: a runtime error, which the
            // interpreter reports).
            Some(Shape::Map { key, range }) => {
                if let Ok(rank) = tlx_layout::layout::rank(&key, &Value::Str(sym)) {
                    return self.map_get(r, int_lit(rank as i64), &range);
                }
            }
            _ => {}
        }
        if let Some(v) = typed::const_of(&r).and_then(|v| tlx_value::ops::field(&v, sym).ok()) {
            return const_expr(v);
        }
        Expr::new(Ty::Val, ExprKind::ValField(to_val(r), sym))
    }

    /// Location and shape of field `f` of a record shape (interning the
    /// shapes of the fields before it).
    fn field_slot(&mut self, fields: &[(Sym, Shape)], f: Sym) -> Option<(FieldLoc, Shape)> {
        let fl = FieldLayout::of_shapes(fields.iter().map(|(_, fs)| fs));
        for ((name, fs), &loc) in fields.iter().zip(fl.locs.iter()) {
            if *name == f {
                return Some((loc, fs.clone()));
            }
            self.sid(fs);
        }
        None
    }

    /// `r.f` for a union of records: one location per arm, if the field has
    /// the same shape (or an integer shape) in every arm that has it.
    fn union_field(&mut self, r: Expr, arms: &[Shape], f: Sym) -> Option<Expr> {
        let mut found: Vec<Option<(FieldLoc, Shape)>> = Vec::new();
        for arm in arms {
            found.push(match arm {
                Shape::Record(fields) => self.field_slot(fields, f),
                _ => None,
            });
        }
        let shapes: Vec<&Shape> = found.iter().flatten().map(|(_, s)| s).collect();
        let first = (*shapes.first()?).clone();
        if shapes.iter().all(|s| **s == first) {
            let fsid = self.sid(&first);
            let locs: Vec<Option<FieldLoc>> = found.iter().map(|h| h.as_ref().map(|(o, _)| *o)).collect();
            return Some(Expr::new(Ty::Enc(fsid), ExprKind::UnionField { base: r, locs: locs.into() }));
        }
        if shapes.iter().all(|s| matches!(s, Shape::Int { .. })) {
            let entries: Vec<Option<(FieldLoc, i64)>> = found
                .iter()
                .map(|h| match h {
                    Some((o, Shape::Int { lo, .. })) => Some((*o, *lo)),
                    _ => None,
                })
                .collect();
            return Some(Expr::new(Ty::Int, ExprKind::UnionFieldInt { base: r, entries: entries.into() }));
        }
        self.union_field_universe(r, arms.len(), &found)
    }

    /// `r.f` for a union of records whose arms store the field as an atom of
    /// a *per-arm* universe: the layout gives each arm a universe as wide as
    /// the atoms seen in that arm, so the same field arrives in as many
    /// encodings as there are arms. Re-encode each arm's slot into the union
    /// of those universes, which keeps the field encoded: a comparison or a
    /// function application on it is then native, while the boxed `ValField`
    /// fallback decodes the whole record and puts both back in the host
    /// (the widest interpreter region of the Raft models).
    fn union_field_universe(&mut self, r: Expr, arms: usize, found: &[Option<(FieldLoc, Shape)>]) -> Option<Expr> {
        let mut univ: Vec<Value> = Vec::new();
        for (_, s) in found.iter().flatten() {
            match s {
                Shape::Atom(u) => univ.extend(u.iter().cloned()),
                _ => return None,
            }
        }
        // One kind of atom only: model values and strings are each ordered
        // by their symbol, but the two are not comparable with one another.
        let model_values = univ.iter().all(|v| matches!(v, Value::ModelValue(_)));
        if !model_values && !univ.iter().all(|v| matches!(v, Value::Str(_))) {
            return None;
        }
        univ.sort();
        univ.dedup();
        let tsid = self.sid(&Shape::Atom(univ.into()));
        let (base, bind) = self.share(r);
        let tag = self.int_word(base.clone(), 0, arms as i64 - 1);
        let mut x = Expr::new(Ty::Enc(tsid), ExprKind::Fail("arm of a record union without the field".into()));
        for (i, entry) in found.iter().enumerate().rev() {
            let Some((loc, shape)) = entry else { continue };
            let ssid = self.sid(shape);
            let slot = Expr::new(Ty::Enc(ssid), ExprKind::Slice { base: base.clone(), loc: loc.offset_words(1) });
            let value = if ssid == tsid { slot } else { self.recode(&slot, tsid)? };
            x = Expr::new(Ty::Enc(tsid), ExprKind::If(eq(tag.clone(), int_lit(i as i64)), value, x));
        }
        Some(let_in(bind, x))
    }

    /// `f[arg]`.
    pub(super) fn typed_fn_app(&mut self, func: &hir::Expr, arg: &hir::Expr, env: &LEnv, st: &St) -> Expr {
        if let Some(x) = self.inline_fn_def(func, std::slice::from_ref(arg), env, st) {
            return x;
        }
        if let Some((c, cenv)) = self.literal_component(func, arg, env) {
            return self.expr(&c, &cenv, st);
        }
        let f = self.expr(func, env, st);
        let f = self.encode_const_fn(f);
        if self.is_ref(f.ty) {
            let k = self.ref_expr(arg, env, st);
            return self.ref_op(crate::ir::RefOp::Apply, vec![f, k]);
        }
        if let Some((key, range)) = self.map_parts(f.ty) {
            if let Some(r) = self.map_key_rank_hir(&key, arg, env, st) {
                return self.map_get(f, r, &range);
            }
        }
        // A tuple key on a product domain: f[<<a, b>>].
        if let (Some(Shape::Fcn { dom, .. }), Some((t, tenv))) = (self.shape_of(f.ty).cloned(), self.peel(arg, env)) {
            if let H::Tuple(es) = &*t.kind {
                if es.len() >= 2 && matches!(dom.first(), Some(Value::Tuple(_))) {
                    let comps: Vec<Expr> = es.iter().map(|e| self.expr(e, &tenv, st)).collect();
                    if let Some(x) = self.apply_product(f.clone(), comps) {
                        return x;
                    }
                }
            }
        }
        let a = self.expr(arg, env, st);
        if let Some(x) = self.apply_union(&f, &a) {
            return x;
        }
        if let (Some(Shape::Fcn { dom, .. }), Some(Shape::Tuple(parts))) = (self.shape_of(f.ty).cloned(), self.shape_of(a.ty).cloned()) {
            if matches!(dom.first(), Some(Value::Tuple(_))) && !matches!(&*a.kind, ExprKind::Const(_)) {
                let (a, bind) = self.share(a);
                let fl = FieldLayout::of_shapes(parts.iter());
                let mut comps = Vec::with_capacity(parts.len());
                for (p, &loc) in parts.iter().zip(fl.locs.iter()) {
                    let psid = self.sid(p);
                    comps.push(Expr::new(Ty::Enc(psid), ExprKind::Slice { base: a.clone(), loc }));
                }
                if let Some(x) = self.apply_product(f.clone(), comps) {
                    return let_in(bind, x);
                }
                return self.apply_enc(f, a);
            }
        }
        self.apply_enc(f, a)
    }

    /// A constant function applied to a computed argument: encoded.
    pub(super) fn encode_const_fn(&mut self, f: Expr) -> Expr {
        match &*f.kind {
            ExprKind::Const(v @ (Value::Fcn(..) | Value::Tuple(_) | Value::Record(_))) if f.ty == Ty::Val => {
                let enc = self.fit_shape(std::slice::from_ref(v)).and_then(|s| {
                    let sid = self.sid(&s);
                    self.const_words(v, sid)
                });
                enc.unwrap_or(f)
            }
            _ => f,
        }
    }

    /// `f[a]` on an encoded function-like value (boxed if not typeable).
    fn apply_enc(&mut self, f: Expr, a: Expr) -> Expr {
        // A union argument of a function over atoms: its atom arm.
        let a = match self.shape_of(f.ty) {
            Some(Shape::Fcn { dom, .. }) if !matches!(dom.first(), Some(Value::Int(_) | Value::Tuple(_))) => {
                self.narrow_union(a, |s| matches!(s, Shape::Atom(_)))
            }
            Some(Shape::Record(_)) => self.narrow_union(a, |s| matches!(s, Shape::Atom(_))),
            _ => a,
        };
        if let Some((key, range)) = self.map_parts(f.ty) {
            if let Some(r) = self.map_key_rank(&key, a.clone()) {
                return self.map_get(f, r, &range);
            }
        }
        if let Some(Shape::Seq { elem, .. }) = self.shape_of(f.ty).cloned() {
            if let Ok(ai) = self.as_int(a.clone()) {
                return self.seq_index(f, ai, &elem);
            }
        }
        // A function of a fixed domain applied to a constant outside it: a
        // runtime error.
        if let (Some(shape), ExprKind::Const(k)) = (self.shape_of(f.ty).cloned(), &*a.kind) {
            if self.slots(&shape).is_some_and(|ss| !ss.iter().any(|(d, _, _)| d == k)) {
                return Expr::new(Ty::Val, ExprKind::Fail("Attempted to apply a function to an argument not in its domain.".into()));
            }
        }
        match self.select(&f, &a) {
            Some((sel, elem_sid)) => self.apply_sel(f, a, sel, elem_sid),
            None => match (typed::const_of(&f), typed::const_of(&a)) {
                (Some(fv), Some(av)) if tlx_value::ops::apply(&fv, &av).is_ok() => const_expr(tlx_value::ops::apply(&fv, &av).unwrap()),
                _ => Expr::new(Ty::Val, ExprKind::Apply(to_val(f), to_val(a))),
            },
        }
    }

    /// `f[a]` where `f` is a union with function-like arms (e.g. a tuple or
    /// `NIL`, or tuples of different lengths): apply on the arm of the
    /// value; any other arm, or an arm where `a` is statically outside the
    /// domain, is a runtime error (as in TLC), which the interpreter then
    /// reports. Several arms must give results of one representation
    /// (integers are unboxed).
    fn apply_union(&mut self, f: &Expr, a: &Expr) -> Option<Expr> {
        let Some(Shape::Union(arms)) = self.shape_of(f.ty).cloned() else { return None };
        let applicable: Vec<usize> = (0..arms.len())
            .filter(|&i| matches!(arms[i], Shape::Tuple(_) | Shape::Seq { .. } | Shape::Fcn { .. } | Shape::Map { .. } | Shape::Record(_)))
            .collect();
        if applicable.is_empty() {
            return None;
        }
        let (fb, bind) = self.share(f.clone());
        let (a, abind) = if applicable.len() > 1 { self.share(a.clone()) } else { (a.clone(), None) };
        let mut results: Vec<(usize, Expr)> = Vec::new();
        for &i in &applicable {
            let asid = self.sid(&arms[i]);
            let payload = Expr::new(Ty::Enc(asid), ExprKind::Slice { base: fb.clone(), loc: FieldLoc::Words(1) });
            let r = self.apply_enc(payload, a.clone());
            match &*r.kind {
                ExprKind::Fail(_) => continue,
                _ if r.ty == Ty::Val => return None,
                _ => results.push((i, r)),
            }
        }
        if results.is_empty() {
            return None;
        }
        if results.windows(2).any(|w| w[0].1.ty != w[1].1.ty) {
            // Integers of different ranges: unboxed.
            let ints: Option<Vec<(usize, Expr)>> = results.iter().map(|(i, r)| self.as_int(r.clone()).ok().map(|x| (*i, x))).collect();
            results = ints?;
        }
        let ty = results[0].1.ty;
        let tag = self.int_word(fb, 0, arms.len() as i64 - 1);
        let mut x = Expr::new(ty, ExprKind::Fail("Attempted to apply a non-function value.".into()));
        for (i, r) in results.into_iter().rev() {
            x = Expr::new(ty, ExprKind::If(eq(tag.clone(), int_lit(i as i64)), r, x));
        }
        Some(let_in(bind.into_iter().chain(abind), x))
    }

    /// `<<e1, ..., en>>[k]` / `[f |-> e, ...]["f"]` for a literal (possibly
    /// behind a definition or a by-name argument) and a constant key: the
    /// component expression.
    fn literal_component(&self, func: &hir::Expr, arg: &hir::Expr, env: &LEnv) -> Option<(hir::Expr, LEnv)> {
        let (f, fenv) = self.peel_call(func, env)?;
        let key = self.const_value(arg, env)?;
        let (i, es): (usize, Vec<&hir::Expr>) = match (&*f.kind, key) {
            (H::Tuple(es), Value::Int(k)) if k >= 1 && (k as usize) <= es.len() => (k as usize - 1, es.iter().collect()),
            (H::Record(fs), Value::Str(s)) => (fs.iter().position(|(n, _)| Sym::new(n) == s)?, fs.iter().map(|(_, e)| e).collect()),
            _ => return None,
        };
        self.others_infallible(&es, i, &fenv).then(|| (es[i].clone(), fenv))
    }

    /// Whether the components of a tuple or record literal other than the
    /// `i`-th cannot fail: only then may a projection skip them (TLC
    /// evaluates the whole literal, so an error in any component is
    /// reported).
    pub(super) fn others_infallible(&self, es: &[&hir::Expr], i: usize, env: &LEnv) -> bool {
        es.iter().enumerate().all(|(j, e)| j == i || self.infallible(e, env))
    }

    /// A conservative check that evaluating `e` cannot fail: constants,
    /// variables, bound values, and tuples/records/sets of them.
    fn infallible(&self, e: &hir::Expr, env: &LEnv) -> bool {
        match &*e.kind {
            H::Num(_) | H::Str(_) | H::Bool(_) | H::Var(_) => true,
            H::Local(l) => matches!(env.lookup(*l, &self.ip.prog), Some(LBind::Ir(_))),
            H::Tuple(es) | H::SetEnum(es) => es.iter().all(|x| self.infallible(x, env)),
            H::Record(fs) => fs.iter().all(|(_, x)| self.infallible(x, env)),
            _ => self.const_value(e, env).is_some(),
        }
    }

    /// How argument `a` selects a slot of encoded function/tuple/record `f`
    /// (and the slot's shape).
    pub(super) fn select(&mut self, f: &Expr, a: &Expr) -> Option<(Sel, ShapeId)> {
        let shape = self.shape_of(f.ty)?.clone();
        let konst = match &*a.kind {
            ExprKind::Const(v) => Some(v),
            _ => None,
        };
        match shape {
            Shape::Record(fields) => {
                if let Some(Value::Str(sym)) = konst {
                    let (loc, fs) = self.field_slot(&fields, *sym)?;
                    return Some((Sel::Loc(loc), self.sid(&fs)));
                }
                // A computed string key of a record with fields of one shape
                // (e.g. a function over a set of strings).
                let Some(Shape::Atom(univ)) = self.shape_of(a.ty).cloned() else { return None };
                let first = fields.first()?.1.clone();
                if fields.iter().any(|(_, f)| *f != first) {
                    return None;
                }
                let table: Vec<i32> =
                    univ.iter().map(|u| fields.iter().position(|(n, _)| *u == Value::Str(*n)).map_or(-1, |p| p as i32)).collect();
                let slot = SlotLayout::of(&first);
                Some((Sel::Index(IndexMap::Table(table.into()), slot), self.sid(&first)))
            }
            Shape::Tuple(elems) => {
                if let Some(Value::Int(k)) = konst {
                    if *k < 1 || *k as usize > elems.len() {
                        return None;
                    }
                    let k = *k as usize;
                    let fl = FieldLayout::of_shapes(elems.iter());
                    for es in &elems[..k - 1] {
                        self.sid(es);
                    }
                    return Some((Sel::Loc(fl.locs[k - 1]), self.sid(&elems[k - 1])));
                }
                // Dynamic index: only for homogeneous tuples.
                let first = elems.first()?.clone();
                if elems.iter().any(|e| *e != first) || !self.int_like(a) {
                    return None;
                }
                let slot = SlotLayout::of(&first);
                Some((Sel::Index(IndexMap::IntRange { lo: 1, n: elems.len() as u32 }, slot), self.sid(&first)))
            }
            Shape::Fcn { dom, range } => {
                let slot = SlotLayout::of(&range);
                let rsid = self.sid(&range);
                if let Some(k) = konst {
                    let pos = dom.iter().position(|d| d == k)?;
                    return Some((Sel::Loc(slot.loc(0, pos)), rsid));
                }
                // Contiguous integer domain.
                if self.int_like(a) {
                    if let Some(Value::Int(lo)) = dom.first() {
                        let contiguous = dom.iter().enumerate().all(|(i, d)| *d == Value::Int(lo + i as i64));
                        if contiguous {
                            return Some((Sel::Index(IndexMap::IntRange { lo: *lo, n: dom.len() as u32 }, slot), rsid));
                        }
                    }
                    return None;
                }
                // Atom argument: table from its universe to domain positions.
                if let Some(Shape::Atom(univ)) = self.shape_of(a.ty) {
                    let table: Vec<i32> = univ.iter().map(|u| dom.iter().position(|d| d == u).map_or(-1, |p| p as i32)).collect();
                    return Some((Sel::Index(IndexMap::Table(table.into()), slot), rsid));
                }
                // A flat product argument (e.g. a tuple of atoms) of a
                // function over some such tuples: the position from a
                // constant table indexed by the argument's rank.
                let ashape = self.shape_of(a.ty)?.clone();
                let radices = flat_radices(&ashape)?;
                let u: u64 = radices.iter().product();
                if u == 0 || u > 4096 {
                    return None;
                }
                let n = dom.len() as i64;
                // Positions encoded in full-width Int{-1..i64::MAX} (word = position + 1).
                let mut table = vec![0u64; u as usize];
                for (i, d) in dom.iter().enumerate() {
                    if let Ok(r) = tlx_layout::layout::rank(&ashape, d) {
                        table[r as usize] = i as u64 + 1;
                    }
                }
                let elem_shape = Shape::Int { lo: -1, hi: i64::MAX };
                let psid = self.sid(&elem_shape);
                let tsid = self.sid(&Shape::Tuple(vec![elem_shape; u as usize].into()));
                let rank = Expr::new(Ty::Int, ExprKind::RankFlat { x: a.clone(), radices: radices.into() });
                let base = Expr::new(Ty::Enc(tsid), ExprKind::ConstWords(table.into()));
                let idx_slot = Expr::new(
                    Ty::Enc(psid),
                    ExprKind::Index { base, arg: rank, map: IndexMap::IntRange { lo: 0, n: u as u32 }, slot: SlotLayout::Words(1) },
                );
                let pos = Expr::new(Ty::Int, ExprKind::Convert(idx_slot));
                Some((Sel::Pos(pos, n as u32, slot), rsid))
            }
            _ => None,
        }
    }

    /// The slot of `f` that `a` selects (see `select`).
    pub(super) fn apply_sel(&self, f: Expr, a: Expr, sel: Sel, elem_sid: ShapeId) -> Expr {
        let k = match sel {
            Sel::Loc(loc) => ExprKind::Slice { base: f, loc },
            Sel::Index(map, slot) => {
                let arg = self.index_arg(&map, a);
                ExprKind::Index { base: f, arg, map, slot }
            }
            Sel::Pos(pos, n, slot) => ExprKind::Index { base: f, arg: pos, map: IndexMap::IntRange { lo: 0, n }, slot },
        };
        Expr::new(Ty::Enc(elem_sid), k)
    }

    /// The argument of an indexed slot access (unboxed for integer ranges).
    fn index_arg(&self, map: &IndexMap, a: Expr) -> Expr {
        match map {
            IndexMap::IntRange { .. } => either(self.as_int(a)),
            IndexMap::Table(_) => a,
        }
    }

    /// `[b EXCEPT ![k1]... = v1, ...]` on an encoded `b`: updates apply in
    /// order; a path `![a][b]` updates `@[a]` with `[@[a] EXCEPT ![b] = ...]`.
    pub(super) fn typed_except(
        &mut self,
        base: &hir::Expr,
        updates: &[(Vec<hir::ExceptKey>, hir::Expr)],
        env: &LEnv,
        st: &St,
    ) -> Option<Expr> {
        let mut cur = self.expr(base, env, st);
        if self.is_ref(cur.ty) {
            return Some(self.ref_except(cur, updates, env, st));
        }
        if !matches!(cur.ty, Ty::Enc(_)) {
            return None;
        }
        for (keys, val) in updates {
            cur = self.except_path(cur, keys, val, env, st)?;
        }
        Some(cur)
    }

    /// `f[<<k1, ..., kn>>]` on a function whose domain is a product of
    /// integer ranges / atom sets: the slot at the mixed-radix position
    /// (a key outside the domain is a runtime error, as in TLC).
    pub(super) fn apply_product(&mut self, f: Expr, comps: Vec<Expr>) -> Option<Expr> {
        let Some(Shape::Fcn { dom, range }) = self.shape_of(f.ty).cloned() else { return None };
        let (pos, valid, binds) = self.product_key(&dom, comps)?;
        let rsid = self.sid(&range);
        let slot_layout = SlotLayout::of(&range);
        let map = IndexMap::IntRange { lo: 0, n: dom.len() as u32 };
        let slot = Expr::new(Ty::Enc(rsid), ExprKind::Index { base: f, arg: pos, map, slot: slot_layout });
        let fail = Expr::new(Ty::Enc(rsid), ExprKind::Fail("Attempted to apply a function to an argument not in its domain.".into()));
        Some(let_in(binds, Expr::new(Ty::Enc(rsid), ExprKind::If(valid, slot, fail))))
    }

    /// Position of the tuple key `comps` in `dom` (sorted tuples forming a
    /// full product of per-component columns), whether it is in the domain,
    /// and the temps to bind first.
    fn product_key(&mut self, dom: &[Value], comps: Vec<Expr>) -> Option<(Expr, Expr, Vec<(Temp, Expr)>)> {
        let n = comps.len();
        if n < 2 || dom.is_empty() || dom.len() > 1 << 16 {
            return None;
        }
        let mut cols: Vec<Vec<Value>> = vec![Vec::new(); n];
        for d in dom {
            let Value::Tuple(es) = d else { return None };
            if es.len() != n {
                return None;
            }
            for (c, e) in cols.iter_mut().zip(es.iter()) {
                c.push(e.clone());
            }
        }
        for c in cols.iter_mut() {
            c.sort();
            c.dedup();
        }
        // The domain must be exactly the product, in lexicographic order.
        if cols.iter().map(|c| c.len()).product::<usize>() != dom.len() {
            return None;
        }
        let mut binds = Vec::new();
        let mut pos: Option<Expr> = None;
        let mut valid = Vec::new();
        for (col, comp) in cols.iter().zip(comps) {
            let (p, ok) = self.column_position(col, comp)?;
            let (p, b) = self.share(p);
            binds.extend(b);
            if let Some(ok) = ok {
                valid.push(ok(p.clone()));
            }
            let size = int_lit(col.len() as i64);
            pos = Some(match pos {
                None => p,
                Some(acc) => {
                    let scaled = Expr::new(Ty::Int, ExprKind::IntBin(IntOp::Mul, acc, size));
                    Expr::new(Ty::Int, ExprKind::IntBin(IntOp::Add, scaled, p))
                }
            });
        }
        Some((pos?, and_all(valid), binds))
    }

    /// Position of `x` within a sorted column of domain values, and a check
    /// (on the position) that `x` is in the column.
    fn column_position(&mut self, col: &[Value], x: Expr) -> Option<(Expr, Option<Box<dyn Fn(Expr) -> Expr>>)> {
        if let ExprKind::Const(v) = &*x.kind {
            let p = col.iter().position(|c| c == v).map_or(-1, |p| p as i64);
            let ok: Box<dyn Fn(Expr) -> Expr> = Box::new(|p| Expr::new(Ty::Bool, ExprKind::IntCmp(CmpOp::Ge, p, int_lit(0))));
            return Some((int_lit(p), Some(ok)));
        }
        if let Some(Value::Int(lo)) = col.first() {
            let lo = *lo;
            let contiguous = col.iter().enumerate().all(|(i, c)| *c == Value::Int(lo + i as i64));
            if !contiguous {
                return None;
            }
            let xi = self.as_int(x).ok()?;
            let p = Expr::new(Ty::Int, ExprKind::IntBin(IntOp::Sub, xi, int_lit(lo)));
            let hi = col.len() as i64 - 1;
            let ok: Box<dyn Fn(Expr) -> Expr> = Box::new(move |p: Expr| {
                and(vec![
                    Expr::new(Ty::Bool, ExprKind::IntCmp(CmpOp::Ge, p.clone(), int_lit(0))),
                    Expr::new(Ty::Bool, ExprKind::IntCmp(CmpOp::Le, p, int_lit(hi))),
                ])
            });
            return Some((p, Some(ok)));
        }
        let Some(Shape::Atom(univ)) = self.shape_of(x.ty).cloned() else { return None };
        let table: Vec<i32> = univ.iter().map(|u| col.iter().position(|c| c == u).map_or(-1, |p| p as i32)).collect();
        let p = Expr::new(Ty::Int, ExprKind::Lookup { x, table: table.into() });
        let ok: Box<dyn Fn(Expr) -> Expr> = Box::new(|p| Expr::new(Ty::Bool, ExprKind::IntCmp(CmpOp::Ge, p, int_lit(0))));
        Some((p, Some(ok)))
    }

    /// `[b EXCEPT !k1!k2... = val]` on an encoded `b` (the result has `b`'s
    /// encoding). `@` in `val` is the old value at the full path.
    pub(super) fn except_path(&mut self, b: Expr, keys: &[hir::ExceptKey], val: &hir::Expr, env: &LEnv, st: &St) -> Option<Expr> {
        let Ty::Enc(bsid) = b.ty else { return None };
        // Bind the base (and a computed key) once: both are used twice.
        let (b, bind_b) = self.share(b);
        let key = match &keys[0] {
            hir::ExceptKey::Field(f) => val_lit(Value::str(f)),
            hir::ExceptKey::Index(ix) if ix.len() == 1 => {
                // A tuple key on a product domain: ![<<a, b>>] (as `![a, b]`).
                if let (Some(Shape::Fcn { dom, .. }), Some((t, tenv))) = (self.shape_of(b.ty).cloned(), self.peel(&ix[0], env)) {
                    if let H::Tuple(es) = &*t.kind {
                        if es.len() >= 2 && matches!(dom.first(), Some(Value::Tuple(_))) {
                            let comps: Vec<Expr> = es.iter().map(|e| self.expr(e, &tenv, st)).collect();
                            if let Some(x) = self.except_product(b.clone(), bind_b.clone(), comps, keys, val, env, st) {
                                return Some(x);
                            }
                        }
                    }
                }
                self.expr(&ix[0], env, st)
            }
            hir::ExceptKey::Index(ix) => {
                // ![a, b] on a product domain.
                let comps: Vec<Expr> = ix.iter().map(|a| self.expr(a, env, st)).collect();
                return self.except_product(b, bind_b, comps, keys, val, env, st);
            }
        };
        if self.map_parts(b.ty).is_some() {
            let x = self.map_except(b, key, keys, val, env, st)?;
            return Some(let_in(bind_b, x));
        }
        if let Some(Shape::Seq { elem, max_len }) = self.shape_of(b.ty).cloned() {
            let x = self.seq_except(b, key, &elem, max_len, keys, val, env, st)?;
            return Some(let_in(bind_b, x));
        }
        if let (ExprKind::Const(k), Some(shape)) = (&*key.kind, self.shape_of(b.ty).cloned()) {
            // Tuples and records as the interpreter treats them: a key of
            // the wrong kind is an error, one outside the domain leaves the
            // value unchanged.
            match (&shape, k) {
                (Shape::Tuple(es), Value::Int(i)) if *i < 1 || *i as usize > es.len() => return Some(let_in(bind_b, b)),
                (Shape::Tuple(_), Value::Int(_)) => {}
                (Shape::Record(fs), Value::Str(n)) if !fs.iter().any(|(f, _)| f == n) => return Some(let_in(bind_b, b)),
                (Shape::Record(_), Value::Str(_)) => {}
                (Shape::Tuple(_) | Shape::Record(_), _) => {
                    return Some(Expr::new(Ty::Enc(bsid), ExprKind::Fail("EXCEPT with a key of the wrong kind".into())))
                }
                _ => {}
            }
            // A key outside the domain (comparable with its elements, else
            // TLC reports an error) leaves the function unchanged.
            let same_kind = |d: &Value| std::mem::discriminant(d) == std::mem::discriminant(k);
            if self
                .slots(&shape)
                .is_some_and(|ss| !ss.is_empty() && !ss.iter().any(|(d, _, _)| d == k) && ss.iter().all(|(d, _, _)| same_kind(d)))
            {
                return Some(let_in(bind_b, b));
            }
        }
        // A union of function-like arms (e.g. a snapshot that is a function or
        // a placeholder value): the arm's tag selects the one to update.
        if let Some(Shape::Union(_)) = self.shape_of(b.ty) {
            let x = self.except_union(b, key, keys, val, env, st)?;
            return Some(let_in(bind_b, x));
        }
        let x = self.except_at(b, key, keys, val, env, st)?;
        Some(let_in(bind_b, x))
    }

    /// `[b EXCEPT ![k1]... = val]` on an encoded `b` with its first key
    /// `key` already lowered (the caller shares `b`). `@` in `val` is the
    /// old value at the slot `key` selects.
    fn except_at(&mut self, b: Expr, key: Expr, keys: &[hir::ExceptKey], val: &hir::Expr, env: &LEnv, st: &St) -> Option<Expr> {
        let Ty::Enc(bsid) = b.ty else { return None };
        let (key, bind_k) = self.share(key);
        let (sel, elem_sid) = self.select(&b, &key)?;
        let old = self.apply_sel(b.clone(), key.clone(), sel.clone(), elem_sid);
        let v = if keys.len() == 1 {
            // `@` is the old value of the selected slot.
            let saved = self.at.replace(old);
            let v = self.expr_into(val, env, st, elem_sid);
            self.at = saved;
            self.coerce_enc(v, elem_sid)
        } else {
            self.except_path(old, &keys[1..], val, env, st)?
        };
        let k = match sel {
            Sel::Loc(loc) => ExprKind::ExceptAt { base: b, loc, value: v },
            Sel::Index(map, slot) => {
                let arg = self.index_arg(&map, key);
                ExprKind::ExceptIndex { base: b, arg, map, slot, value: v }
            }
            Sel::Pos(pos, n, slot) => ExprKind::ExceptIndex { base: b, arg: pos, map: IndexMap::IntRange { lo: 0, n }, slot, value: v },
        };
        Some(let_in(bind_k, Expr::new(Ty::Enc(bsid), k)))
    }

    /// `[b EXCEPT ![k1]... = val]` on an encoded union `b` with function-like
    /// arms (e.g. a per-transaction snapshot that is a function, or a
    /// placeholder value before the transaction starts): the arm's tag
    /// selects the arm the update applies to, and the union is rebuilt with
    /// the same tag. `key` is evaluated once for every arm, as the
    /// interpreter evaluates the keys of an update before it looks at the
    /// value; the replacement is evaluated only in the arm the value has,
    /// so an update the value does not take leaves it unevaluated, as
    /// `except::update` does. An arm that is not function-like is the
    /// interpreter's non-function error (its `ops::select` refuses it); the
    /// fallback re-runs and reports it.
    fn except_union(&mut self, b: Expr, key: Expr, keys: &[hir::ExceptKey], val: &hir::Expr, env: &LEnv, st: &St) -> Option<Expr> {
        let Ty::Enc(bsid) = b.ty else { return None };
        let Some(Shape::Union(arms)) = self.shape_of(b.ty).cloned() else { return None };
        // (A nested union arm is left to the interpreter rather than guessed
        // at; `union_arms` does not produce one today.)
        if arms.iter().any(|a| matches!(a, Shape::Union(_))) {
            return None;
        }
        let applicable: Vec<usize> = (0..arms.len())
            .filter(|&i| matches!(arms[i], Shape::Record(_) | Shape::Tuple(_) | Shape::Seq { .. } | Shape::Fcn { .. } | Shape::Map { .. }))
            .collect();
        if applicable.is_empty() {
            return None;
        }
        let (key, bind_k) = self.share(key);
        let mut parts: Vec<(usize, Expr)> = Vec::with_capacity(applicable.len());
        for &i in &applicable {
            let asid = self.sid(&arms[i]);
            let payload = Expr::new(Ty::Enc(asid), ExprKind::Slice { base: b.clone(), loc: FieldLoc::Words(1) });
            let r = self.except_at(payload, key.clone(), keys, val, env, st)?;
            // Arm index, then the arm's encoding padded to the widest arm.
            parts.push((i, self.union_arm_coerce(&r, bsid)?));
        }
        let tag = self.int_word(b, 0, arms.len() as i64 - 1);
        let mut x = Expr::new(Ty::Enc(bsid), ExprKind::Fail("EXCEPT applied to a value that is not a function".into()));
        for (i, r) in parts.into_iter().rev() {
            x = Expr::new(Ty::Enc(bsid), ExprKind::If(eq(tag.clone(), int_lit(i as i64)), r, x));
        }
        Some(let_in(bind_k, x))
    }

    /// `(k :> v) @@ g` built into the fixed-domain function shape `sid`
    /// when `k` is statically in the domain: `g` with the slot of `k` set
    /// to `v` (the domain stays that of `g`). None otherwise.
    pub(super) fn fcn_merge_into(&mut self, f: &hir::Expr, g: &hir::Expr, env: &LEnv, st: &St, sid: ShapeId) -> Option<Expr> {
        let (p, penv) = self.peel(f, env)?;
        let H::Builtin { op: B::ColonGt, args } = &*p.kind else { return None };
        if self.ip.is_builtin_overridden(B::ColonGt) {
            return None;
        }
        let key = self.expr(&args[0], &penv, st);
        if !is_trivial(&key) {
            return None;
        }
        let base = self.expr_into(g, env, st, sid);
        if base.ty != Ty::Enc(sid) {
            return None;
        }
        let (b, bind_b) = self.share(base);
        let (sel, elem_sid) = self.select(&b, &key)?;
        // (`select` gives a fixed location only for a constant key in the
        // domain; a computed key must be in it whatever its value.)
        if matches!(sel, Sel::Index(..) | Sel::Pos(..)) && !self.cannot_fail(&self.apply_sel(b.clone(), key.clone(), sel.clone(), elem_sid))
        {
            return None;
        }
        let v = self.expr_into(&args[1], &penv, st, elem_sid);
        let v = self.coerce_enc(v, elem_sid);
        let k = match sel {
            Sel::Loc(loc) => ExprKind::ExceptAt { base: b, loc, value: v },
            Sel::Index(map, slot) => {
                let arg = self.index_arg(&map, key);
                ExprKind::ExceptIndex { base: b, arg, map, slot, value: v }
            }
            Sel::Pos(..) => return None,
        };
        Some(let_in(bind_b, Expr::new(Ty::Enc(sid), k)))
    }

    /// `[s EXCEPT ![i]... = v]` on an encoded sequence: the slots after the
    /// length word updated at `i` if `1 <= i <= Len(s)`, else `s` unchanged
    /// (as in TLC).
    #[allow(clippy::too_many_arguments)]
    fn seq_except(
        &mut self,
        b: Expr,
        key: Expr,
        elem: &Shape,
        max_len: usize,
        keys: &[hir::ExceptKey],
        val: &hir::Expr,
        env: &LEnv,
        st: &St,
    ) -> Option<Expr> {
        let Ty::Enc(bsid) = b.ty else { return None };
        let i = self.as_int(key).ok()?;
        let (i, bind_i) = self.share(i);
        let esid = self.sid(elem);
        let slot = SlotLayout::of(elem);
        let old = Expr::new(Ty::Enc(esid), ExprKind::SeqIndex { base: b.clone(), arg: i.clone(), slot });
        let v = if keys.len() == 1 {
            let saved = self.at.replace(old);
            let v = self.expr_into(val, env, st, esid);
            self.at = saved;
            self.coerce_enc(v, esid)
        } else {
            self.except_path(old, &keys[1..], val, env, st)?
        };
        let lsid = self.sid(&Shape::Int { lo: 0, hi: max_len as i64 });
        let ssid = self.sid(&Shape::Tuple(vec![elem.clone(); max_len].into()));
        let len_word = Expr::new(Ty::Enc(lsid), ExprKind::Slice { base: b.clone(), loc: FieldLoc::Words(0) });
        let slots = Expr::new(Ty::Enc(ssid), ExprKind::Slice { base: b.clone(), loc: FieldLoc::Words(1) });
        let upd = Expr::new(
            Ty::Enc(ssid),
            ExprKind::ExceptIndex { base: slots, arg: i.clone(), map: IndexMap::IntRange { lo: 1, n: max_len as u32 }, slot, value: v },
        );
        let new = Expr::new(Ty::Enc(bsid), ExprKind::Concat(vec![len_word, upd]));
        let len = Expr::new(Ty::Int, ExprKind::SeqLen(b.clone()));
        let inside = and(vec![
            Expr::new(Ty::Bool, ExprKind::IntCmp(CmpOp::Ge, i.clone(), int_lit(1))),
            Expr::new(Ty::Bool, ExprKind::IntCmp(CmpOp::Le, i, len)),
        ]);
        Some(let_in(bind_i, Expr::new(Ty::Enc(bsid), ExprKind::If(inside, new, b))))
    }

    /// `except_path` whose first key is a tuple on a product domain.
    #[allow(clippy::too_many_arguments)]
    fn except_product(
        &mut self,
        b: Expr,
        bind_b: Option<(Temp, Expr)>,
        comps: Vec<Expr>,
        keys: &[hir::ExceptKey],
        val: &hir::Expr,
        env: &LEnv,
        st: &St,
    ) -> Option<Expr> {
        let Ty::Enc(bsid) = b.ty else { return None };
        let Some(Shape::Fcn { dom, range }) = self.shape_of(b.ty).cloned() else { return None };
        let (pos, valid, binds) = self.product_key(&dom, comps)?;
        let (pos, bind_p) = self.share(pos);
        let rsid = self.sid(&range);
        let slot = SlotLayout::of(&range);
        let map = IndexMap::IntRange { lo: 0, n: dom.len() as u32 };
        let old = Expr::new(Ty::Enc(rsid), ExprKind::Index { base: b.clone(), arg: pos.clone(), map: map.clone(), slot });
        let v = if keys.len() == 1 {
            let saved = self.at.replace(old);
            let v = self.expr_into(val, env, st, rsid);
            self.at = saved;
            self.coerce_enc(v, rsid)
        } else {
            self.except_path(old, &keys[1..], val, env, st)?
        };
        let upd = Expr::new(Ty::Enc(bsid), ExprKind::ExceptIndex { base: b.clone(), arg: pos, map, slot, value: v });
        // TLC: EXCEPT on a key outside the domain leaves the function unchanged.
        let x = Expr::new(Ty::Enc(bsid), ExprKind::If(valid, upd, b));
        Some(let_in(bind_p.into_iter().chain(binds).chain(bind_b), x))
    }

    /// Element `i` (1-based, unboxed) of an encoded sequence.
    pub(super) fn seq_index(&mut self, s: Expr, i: Expr, elem: &Shape) -> Expr {
        let esid = self.sid(elem);
        let slot = SlotLayout::of(elem);
        Expr::new(Ty::Enc(esid), ExprKind::SeqIndex { base: s, arg: i, slot })
    }

    /// `Len(s)`.
    pub(super) fn typed_len(&mut self, s: &hir::Expr, env: &LEnv, st: &St) -> Expr {
        let s = self.expr(s, env, st);
        if self.is_ref(s.ty) {
            return self.ref_op(crate::ir::RefOp::Len, vec![s]);
        }
        match self.shape_of(s.ty) {
            Some(Shape::Seq { .. }) => return Expr::new(Ty::Int, ExprKind::SeqLen(s)),
            // Fixed-length tuples: a constant (after the operand).
            Some(Shape::Tuple(es)) => {
                let n = es.len() as i64;
                return self.after_eval(s, int_lit(n));
            }
            // A union with tuple / sequence arms: by the arm (any other
            // arm is a runtime error).
            Some(Shape::Union(arms)) if arms.iter().any(|a| matches!(a, Shape::Tuple(_) | Shape::Seq { .. })) => {
                let arms = arms.clone();
                let (u, bind) = self.share(s);
                let tag = self.int_word(u.clone(), 0, arms.len() as i64 - 1);
                let mut x = Expr::new(Ty::Int, ExprKind::Fail("Len of a non-sequence".into()));
                for (i, a) in arms.iter().enumerate().rev() {
                    let len = match a {
                        Shape::Tuple(es) => int_lit(es.len() as i64),
                        Shape::Seq { .. } => {
                            let asid = self.sid(a);
                            Expr::new(
                                Ty::Int,
                                ExprKind::SeqLen(Expr::new(Ty::Enc(asid), ExprKind::Slice { base: u.clone(), loc: FieldLoc::Words(1) })),
                            )
                        }
                        _ => continue,
                    };
                    x = Expr::new(Ty::Int, ExprKind::If(eq(tag.clone(), int_lit(i as i64)), len, x));
                }
                return let_in(bind, x);
            }
            _ => {}
        }
        self.val_op(B::Len, vec![s])
    }

    /// `SubSeq(s, m, n)` on an encoded sequence.
    pub(super) fn typed_subseq(&mut self, s: &hir::Expr, m: &hir::Expr, n: &hir::Expr, env: &LEnv, st: &St) -> Option<Expr> {
        let s = self.expr(s, env, st);
        let s = self.as_seq(s)?;
        let Some(Shape::Seq { elem, .. }) = self.shape_of(s.ty).cloned() else { return None };
        let (lo, hi) = (self.expr(m, env, st), self.expr(n, env, st));
        let (lo, hi) = (self.as_int(lo).ok()?, self.as_int(hi).ok()?);
        self.sid(&elem);
        let slot = SlotLayout::of(&elem);
        let ty = s.ty;
        Some(Expr::new(ty, ExprKind::SeqSub { base: s, lo, hi, slot }))
    }

    /// An encoded sequence, or a homogeneous tuple viewed as a sequence.
    pub(super) fn as_seq(&mut self, x: Expr) -> Option<Expr> {
        if let (Ty::Val, Some(v)) = (x.ty, typed::const_of(&x)) {
            return self.const_seq(&v);
        }
        match self.shape_of(x.ty)?.clone() {
            Shape::Seq { .. } => Some(x),
            Shape::Tuple(es) if !es.is_empty() && es.iter().all(|e| *e == es[0]) => {
                let sid = self.sid(&Shape::Seq { elem: Box::new(es[0].clone()), max_len: es.len() });
                Some(self.coerce_enc(x, sid))
            }
            _ => None,
        }
    }

    /// A constant non-empty sequence encoded as a sequence of its length.
    fn const_seq(&mut self, v: &Value) -> Option<Expr> {
        let Value::Tuple(es) = v else { return None };
        let elem = self.fit_shape(es)?;
        let sid = self.sid(&Shape::Seq { elem: Box::new(elem), max_len: es.len() });
        self.const_words(v, sid)
    }

    /// `DOMAIN f` of an encoded function-like value: a constant for fixed
    /// domains, `1..Len(s)` for sequences (`None`: boxed).
    pub(super) fn typed_domain(&mut self, f: &hir::Expr, env: &LEnv, st: &St) -> Option<Expr> {
        let x = self.expr(f, env, st);
        // A domain fixed by the shape: the operand is still evaluated (TLC
        // reports its errors, e.g. a division by zero in an EXCEPT value).
        let fixed = |me: &mut Self, x: Expr, d: Value| me.after_eval(x, val_lit(d));
        if self.is_ref(x.ty) {
            return Some(self.ref_op(crate::ir::RefOp::Domain, vec![x]));
        }
        match self.shape_of(x.ty)?.clone() {
            Shape::Tuple(es) => Some(fixed(self, x, Value::Interval(1, es.len() as i64))),
            Shape::Map { key, .. } => Some(self.map_domain(x, &key)),
            Shape::Fcn { dom, .. } => {
                let d = Value::set_from(dom.to_vec()).ok()?;
                Some(fixed(self, x, d))
            }
            Shape::Record(fs) => {
                let d = Value::set_from(fs.iter().map(|(n, _)| Value::Str(*n)).collect()).ok()?;
                Some(fixed(self, x, d))
            }
            Shape::Seq { .. } => {
                let len = Expr::new(Ty::Int, ExprKind::SeqLen(x));
                Some(Expr::new(Ty::Val, ExprKind::ValOp { op: B::DotDot, args: vec![to_val(int_lit(1)), to_val(len)] }))
            }
            _ => None,
        }
    }

    /// `Head(s)`.
    pub(super) fn typed_head(&mut self, s: &hir::Expr, env: &LEnv, st: &St) -> Expr {
        let s = self.expr(s, env, st);
        if self.is_ref(s.ty) {
            return self.ref_op(crate::ir::RefOp::Head, vec![s]);
        }
        if let Some(Shape::Seq { elem, .. }) = self.shape_of(s.ty).cloned() {
            return self.seq_index(s, int_lit(1), &elem);
        }
        self.val_op(B::Head, vec![s])
    }

    /// `Tail(s)`.
    pub(super) fn typed_tail(&mut self, s: &hir::Expr, env: &LEnv, st: &St) -> Expr {
        let s = self.expr(s, env, st);
        if self.is_ref(s.ty) {
            return self.ref_op(crate::ir::RefOp::Tail, vec![s]);
        }
        if let Some(Shape::Seq { elem, .. }) = self.shape_of(s.ty).cloned() {
            self.sid(&elem);
            let slot = SlotLayout::of(&elem);
            return Expr::new(s.ty, ExprKind::SeqTail { base: s, slot });
        }
        self.val_op(B::Tail, vec![s])
    }

    /// `a \o b` when one side is an encoded sequence (the other is built in
    /// the same encoding).
    pub(super) fn typed_concat(&mut self, a: &hir::Expr, b: &hir::Expr, env: &LEnv, st: &St) -> Expr {
        let (la, lb) = if self.constructs(a, env) {
            let lb = self.expr(b, env, st);
            match lb.ty {
                Ty::Enc(sid) => (self.expr_into(a, env, st, sid), lb),
                _ => {
                    // `b` untyped on its own (e.g. a recursive operator whose
                    // result representation is not inferred): into `a`'s.
                    let la = self.expr(a, env, st);
                    match la.ty {
                        Ty::Enc(sid) if !matches!(&*lb.kind, ExprKind::Const(_)) => {
                            let lb = self.expr_into(b, env, st, sid);
                            (la, lb)
                        }
                        _ => (la, lb),
                    }
                }
            }
        } else {
            let la = self.expr(a, env, st);
            match la.ty {
                Ty::Enc(sid) => {
                    let lb = self.expr_into(b, env, st, sid);
                    (la, lb)
                }
                _ => {
                    let lb = self.expr(b, env, st);
                    (la, lb)
                }
            }
        };
        // A constant operand: in the other operand's encoding if it fits.
        let (la, lb) = match (la.ty, lb.ty) {
            (Ty::Enc(sid), Ty::Val) => {
                let lb = typed::const_of(&lb).and_then(|v| self.const_words(&v, sid)).unwrap_or(lb);
                (la, lb)
            }
            (Ty::Val, Ty::Enc(sid)) => {
                let la = typed::const_of(&la).and_then(|v| self.const_words(&v, sid)).unwrap_or(la);
                (la, lb)
            }
            _ => (la, lb),
        };
        if la.ty != Ty::Val || lb.ty != Ty::Val {
            if let (Some(sa), Some(sb)) = (self.as_seq(la.clone()), self.as_seq(lb.clone())) {
                if let (Some(Shape::Seq { elem: ea, max_len: ma }), Some(Shape::Seq { elem: eb, max_len: mb })) =
                    (self.shape_of(sa.ty).cloned(), self.shape_of(sb.ty).cloned())
                {
                    if ea == eb {
                        // Room for both operands.
                        let max_len = ma + mb;
                        let sid = self.sid(&Shape::Seq { elem: ea.clone(), max_len });
                        let (a2, b2) = (self.coerce_enc(sa, sid), self.coerce_enc(sb, sid));
                        self.sid(&ea);
                        let slot = SlotLayout::of(&ea);
                        return Expr::new(Ty::Enc(sid), ExprKind::SeqConcat { a: a2, b: b2, slot, max_len: max_len as u32 });
                    }
                }
            }
        }
        self.val_op(B::Concat, vec![la, lb])
    }

    /// `Append(s, x)`.
    pub(super) fn typed_append(&mut self, s: &hir::Expr, x: &hir::Expr, env: &LEnv, st: &St) -> Expr {
        let s = self.expr(s, env, st);
        if self.is_ref(s.ty) {
            let x = self.ref_expr(x, env, st);
            return self.ref_op(crate::ir::RefOp::Append, vec![s, x]);
        }
        if let Some(Shape::Seq { elem, max_len }) = self.shape_of(s.ty).cloned() {
            let esid = self.sid(&elem);
            let slot = SlotLayout::of(&elem);
            let x = self.expr_into(x, env, st, esid);
            return Expr::new(s.ty, ExprKind::SeqAppend { base: s, value: x, slot, max_len: max_len as u32 });
        }
        let x = self.expr(x, env, st);
        self.val_op(B::Append, vec![s, x])
    }
}
