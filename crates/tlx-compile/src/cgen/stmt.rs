//! C generation for statements and loops over iteration sources.

use std::fmt::Write;

use tlx_layout::layout::bitset_universe;
use tlx_layout::Shape;

use super::{no, temp, CGen, R};
use crate::inplace::Plan;
use crate::ir::*;

impl CGen<'_> {
    /// Append the code of `s` (indented `ind` levels) to `out`.
    pub(super) fn stmt(&mut self, s: &Stmt, ind: usize, out: &mut String) -> R<()> {
        let pad = "  ".repeat(ind.min(8));
        match s {
            Stmt::Compose { .. } => return no("action composition uses the compiled executor"),
            Stmt::Stop => {}
            Stmt::Emit => match &self.emit_target {
                Some((flag, label)) => writeln!(out, "{pad}{{ {flag} = 1; goto {label}; }}").unwrap(),
                None => writeln!(out, "{pad}if (h->emit(cx, s1, 0)) return TLX_STOP;").unwrap(),
            },
            Stmt::Branches(bs) => {
                for b in bs {
                    writeln!(out, "{pad}{{").unwrap();
                    self.stmt(b, ind + 1, out)?;
                    writeln!(out, "{pad}}}").unwrap();
                }
            }
            Stmt::Guard { cond, then } => {
                let c = self.bool_expr(cond)?;
                writeln!(out, "{pad}if ({c}) {{").unwrap();
                self.stmt(then, ind + 1, out)?;
                writeln!(out, "{pad}}}").unwrap();
            }
            Stmt::If { cond, then, els } => {
                let c = self.bool_expr(cond)?;
                writeln!(out, "{pad}if ({c}) {{").unwrap();
                self.stmt(then, ind + 1, out)?;
                writeln!(out, "{pad}}} else {{").unwrap();
                self.stmt(els, ind + 1, out)?;
                writeln!(out, "{pad}}}").unwrap();
            }
            Stmt::Then { first, assigned, rest } => {
                let k = self.fresh();
                let (flag, label) = (format!("jn{k}"), format!("jn{k}_done"));
                writeln!(out, "{pad}{{ int {flag} = 0;").unwrap();
                let saved = self.emit_target.replace((flag.clone(), label.clone()));
                let r = self.stmt(first, ind + 1, out);
                self.emit_target = saved;
                r?;
                writeln!(out, "{pad}{label}: ; if ({flag}) {{").unwrap();
                let outer_assigned = self.assigned.clone();
                for (a, b) in self.assigned.iter_mut().zip(assigned) {
                    *a |= *b;
                }
                let r = self.stmt(rest, ind + 1, out);
                self.assigned = outer_assigned;
                r?;
                writeln!(out, "{pad}}} }}").unwrap();
            }
            Stmt::Let { temp: t, value, body } => {
                let v = self.expr(value)?;
                let ct = self.c_ty(value.ty)?;
                writeln!(out, "{pad}{{ {ct} {} = {v};", temp(*t)).unwrap();
                self.stmt(body, ind + 1, out)?;
                writeln!(out, "{pad}}}").unwrap();
            }
            Stmt::ForEach { bind, set, iter, body } => {
                let h0 = self.handles;
                let mut inner = String::new();
                self.loop_body(*bind, body, |g| g.stmt(body, ind + 2, &mut inner))?;
                // (A guarded body does nothing where its guard is false.)
                let pred = match &**body {
                    Stmt::Guard { cond, .. } => Some(cond),
                    _ => None,
                };
                let sorted = match iter {
                    IterMode::Enumerate => Some(false),
                    IterMode::Normalized => Some(true),
                    // A quantifier's bound domain: in mixed mode `h->elems`
                    // calls `ops::enumerate`, which enforces `-maxSetSize` and
                    // falls back to the interpreter on overflow or streaming
                    // domains (`SUBSET S`).
                    IterMode::Bound => Some(false),
                };
                let lp = self.foreach(*bind, set, &inner, ind, h0, sorted, pred)?;
                out.push_str(&lp);
            }
            Stmt::Assign { var, value, body } => {
                // Computed in place into the next state (an update writes
                // only its slots; `inplace`). The words of an unassigned
                // variable are never read (`NextVar` reads assigned ones,
                // regions get the statically assigned set, `Emit` runs
                // when all are assigned), so nothing is restored.
                let i = *var as usize;
                let sid = self.ty.var_sid[i];
                let off = self.ty.var_offset(i);
                let n = self.words(sid);
                let d = format!("d{}", self.fresh());
                let mut code = String::new();
                let planned = if value.ty == Ty::Enc(sid) {
                    let snap = self.snapshot();
                    let r = self.plan_into(&crate::inplace::plan(value, self.ty), &d, ind.min(8) + 1, &mut code);
                    if r.is_err() {
                        self.rollback(snap);
                        code.clear();
                    }
                    r.is_ok()
                } else {
                    false
                };
                if !planned {
                    let src = self.encoded(value, sid)?;
                    writeln!(code, "{pad}  memmove({d}, {src}, {n} * 8);").unwrap();
                }
                writeln!(out, "{pad}{{ uint64_t *{d} = s1 + {off};").unwrap();
                out.push_str(&code);
                writeln!(out, "{pad}}}").unwrap();
                let was = std::mem::replace(&mut self.assigned[i], true);
                let r = self.stmt(body, ind, out);
                self.assigned[i] = was;
                r?;
            }
            Stmt::Error(_) => writeln!(out, "{pad}return TLX_ERR;").unwrap(),
            Stmt::Count(id) => writeln!(out, "{pad}cnt{id}++;").unwrap(),
            Stmt::Repeat { id, bind, set, body, rest } => {
                // tot = product over the elements of the paths through body
                // (stopping at 0); then run rest tot times.
                let h0 = self.handles;
                let mut inner = String::new();
                writeln!(inner, "{pad}    {{ uint64_t cnt{id} = 0;").unwrap();
                self.loop_body(*bind, body, |g| g.stmt(body, ind + 3, &mut inner))?;
                writeln!(
                    inner,
                    "{pad}    if (!cnt{id}) {{ tot{id} = 0; goto rep{id}_done; }} \
                     if (tot{id} > UINT64_MAX / cnt{id}) tot{id} = UINT64_MAX; else tot{id} *= cnt{id}; }}"
                )
                .unwrap();
                let lp = self.foreach(*bind, set, &inner, ind + 1, h0, Some(false), None)?;
                writeln!(out, "{pad}{{ uint64_t tot{id} = 1;").unwrap();
                out.push_str(&lp);
                writeln!(out, "{pad}  rep{id}_done: ;").unwrap();
                writeln!(out, "{pad}  for (uint64_t rr{id} = 0; rr{id} < tot{id}; rr{id}++) {{").unwrap();
                let h1 = self.handles;
                let mut again = String::new();
                self.stmt(rest, ind + 2, &mut again)?;
                let again = self.released(&again, self.made_handles(h1), &format!("{pad}    "));
                out.push_str(&again);
                writeln!(out, "{pad}  }}").unwrap();
                writeln!(out, "{pad}}}").unwrap();
            }
        }
        Ok(())
    }

    /// Append statements computing the plan `p` into the words at `d` (a
    /// `uint64_t *` variable; see `inplace`).
    pub(super) fn plan_into(&mut self, p: &Plan, d: &str, ind: usize, out: &mut String) -> R<()> {
        let pad = "  ".repeat(ind);
        match p {
            Plan::Keep => {}
            Plan::Copy(e) => {
                let Ty::Enc(sid) = e.ty else { return no("boxed update") };
                let n = self.words(sid);
                let v = self.expr(e)?;
                writeln!(out, "{pad}memmove({d}, {v}, {n} * 8);").unwrap();
            }
            Plan::Let { temp: t, value, body } => {
                let ct = self.c_ty(value.ty)?;
                let v = self.expr(value)?;
                writeln!(out, "{pad}{{ {ct} {} = {v};", temp(*t)).unwrap();
                self.plan_into(body, d, ind + 1, out)?;
                writeln!(out, "{pad}}}").unwrap();
            }
            Plan::LetHere { temp: t, value, body } => {
                self.plan_into(value, d, ind, out)?;
                writeln!(out, "{pad}{{ const uint64_t *{} = {d};", temp(*t)).unwrap();
                self.plan_into(body, d, ind + 1, out)?;
                writeln!(out, "{pad}}}").unwrap();
            }
            Plan::At { base, update } => {
                self.plan_into(base, d, ind, out)?;
                match update {
                    crate::inplace::AtUpdate::Word { offset, value } => {
                        let d1 = format!("d{}", self.fresh());
                        writeln!(out, "{pad}{{ uint64_t *{d1} = {d} + {offset};").unwrap();
                        self.plan_into(value, &d1, ind + 1, out)?;
                        writeln!(out, "{pad}}}").unwrap();
                    }
                    crate::inplace::AtUpdate::Bits { pos, value: Some(ve) } => {
                        let v = self.expr(ve)?;
                        writeln!(out, "{pad}tlx_bset({d}, {}, {}, {}, ({v})[0]);", pos.word, pos.shift, pos.bits).unwrap();
                    }
                    crate::inplace::AtUpdate::Bits { value: None, .. } => {}
                }
            }
            Plan::AtIndex { base, arg, map, update } => {
                self.plan_into(base, d, ind, out)?;
                let k = self.fresh();
                let sl = self.slot_or(arg, map, "-1")?;
                match update {
                    crate::inplace::IndexUpdate::Words { elem_words, value } => {
                        writeln!(out, "{pad}{{ int64_t sl{k} = {sl}; if (sl{k} >= 0) {{ uint64_t *d{k} = {d} + sl{k} * {elem_words};")
                            .unwrap();
                        self.plan_into(value, &format!("d{k}"), ind + 1, out)?;
                        writeln!(out, "{pad}}} }}").unwrap();
                    }
                    crate::inplace::IndexUpdate::Bits { bits, value: Some(ve) } => {
                        let v = self.expr(ve)?;
                        writeln!(
                            out,
                            "{pad}{{ int64_t sl{k} = {sl}; if (sl{k} >= 0) {{ const uint64_t *v{k} = {v}; tlx_sset({d}, {bits}, (uint64_t)sl{k}, v{k}[0]); }} }}"
                        )
                        .unwrap();
                    }
                    crate::inplace::IndexUpdate::Bits { value: None, .. } => {
                        writeln!(out, "{pad}(void)({sl});").unwrap();
                    }
                }
            }
            Plan::If { cond, then, els } => {
                let c = self.bool_expr(cond)?;
                writeln!(out, "{pad}if ({c}) {{").unwrap();
                self.plan_into(then, d, ind + 1, out)?;
                writeln!(out, "{pad}}} else {{").unwrap();
                self.plan_into(els, d, ind + 1, out)?;
                writeln!(out, "{pad}}}").unwrap();
            }
            Plan::Concat(parts) => {
                for (off, part) in parts {
                    let d1 = format!("d{}", self.fresh());
                    writeln!(out, "{pad}{{ uint64_t *{d1} = {d} + {off};").unwrap();
                    self.plan_into(part, &d1, ind + 1, out)?;
                    writeln!(out, "{pad}}}").unwrap();
                }
            }
            Plan::Insert { set, elem, elem_words, max_card } => {
                self.plan_into(set, d, ind, out)?;
                let x = self.expr(elem)?;
                writeln!(out, "{pad}if (!tlx_sorted_add({d}, {x}, {elem_words}, {max_card})) return TLX_ERR;").unwrap();
            }
            Plan::Bits { op, a, b } => {
                self.plan_into(a, d, ind, out)?;
                let Ty::Enc(sid) = b.ty else { return no("boxed set") };
                let n = self.words(sid);
                let y = self.expr(b)?;
                let o = match op {
                    SetOp::Union => "|= y_[i_]",
                    SetOp::Inter => "&= y_[i_]",
                    SetOp::Diff => "&= ~y_[i_]",
                };
                writeln!(out, "{pad}{{ const uint64_t *y_ = {y}; for (int i_ = 0; i_ < {n}; i_++) {d}[i_] {o}; }}").unwrap();
            }
        }
        Ok(())
    }

    /// Generate the body `body` of a statement loop binding `bind` with
    /// `f`, noting (mixed mode) the temps that depend on the element.
    fn loop_body(&mut self, bind: Temp, body: &Stmt, f: impl FnOnce(&mut Self) -> R<()>) -> R<()> {
        if !self.mixing {
            return f(self);
        }
        let mut bound = std::collections::HashSet::from([bind]);
        crate::lower::stmt_bound_temps(body, &mut bound);
        self.stmt_loops.push(bound);
        let r = f(self);
        self.stmt_loops.pop();
        r
    }

    /// Loop over the elements of an iteration source, binding `bind` and
    /// running `body`, which releases the handles it makes if any were made
    /// since `handles` (a value of `self.handles`, taken before generating
    /// `body`). `sorted`: a statement loop (in normalized order if true),
    /// which (mixed mode) may loop over the elements of a boxed set; None:
    /// an expression loop (over typed sources only). `pred`: the body does
    /// nothing for an element on which it is false (a filter, an existential
    /// quantifier...): its leading tests of constant fields select the ranks
    /// of a bitset of union elements looped over (`rankmask`).
    #[allow(clippy::too_many_arguments)] // the loop's source, body text and position, and how it may be narrowed: every caller passes all of them
    pub(super) fn foreach(
        &mut self,
        bind: Temp,
        set: &Expr,
        body: &str,
        ind: usize,
        handles: usize,
        sorted: Option<bool>,
        pred: Option<&Expr>,
    ) -> R<String> {
        let pad = "  ".repeat(ind);
        let body = &self.released(body, self.made_handles(handles), &format!("{pad}  "));
        let t = temp(bind);
        // (A stored set's elements are normalized: also the sorted order.)
        if let ExprKind::RefElems(x) = &*set.kind {
            return self.ref_elems_loop(x, &t, body, &pad);
        }
        if !set.is_typed_source() || sorted == Some(true) {
            if !self.mixing || sorted.is_none() || set.ty != Ty::Val || self.temps[bind as usize] != Ty::Val {
                return no(if sorted == Some(true) { "sorted enumeration" } else { "iteration over a boxed set" });
            }
            // The elements as consecutive handles.
            let s = self.expr(set)?;
            let k = self.fresh();
            self.handles += 1;
            let mut out = String::new();
            writeln!(
                out,
                "{pad}{{ uint64_t f{k}, n{k}; if (h->elems(cx, {s}, {}, &f{k}, &n{k})) return TLX_ERR;",
                (sorted == Some(true)) as u32
            )
            .unwrap();
            writeln!(out, "{pad}for (uint64_t i{k} = 0; i{k} < n{k}; i{k}++) {{ uint64_t {t} = f{k} + i{k};").unwrap();
            out.push_str(body);
            writeln!(out, "{pad}}} }}").unwrap();
            return Ok(out);
        }
        if let ExprKind::OrderedSet { set, plan } = &*set.kind {
            let Ty::Enc(sid) = set.ty else { return no("ordered boxed set") };
            let Shape::Set { elem, max_card } = self.ty.shape(sid).clone() else { return no("ordered non-set") };
            if let Some(u) = bitset_universe(&elem) {
                let nw = self.words(sid);
                let keys = self.static_words(&plan[plan[crate::encoded_order::schema::SPAN] as usize..]);
                let s = self.expr(set)?;
                let k = self.fresh();
                let (en, digits) = self.unrank_code(&elem, k)?;
                return Ok(format!("{pad}{{ uint64_t I{k}[{u}]; uint64_t N{k} = tlx_order_bit_indices({keys}, {s}, {nw}, I{k});\n{pad}for (uint64_t i{k} = 0; i{k} < N{k}; i{k}++) {{ uint64_t q{k} = I{k}[i{k}]; uint64_t R{k}[{en}]; {digits} const uint64_t *{t} = R{k};\n{body}{pad}}} }}\n"));
            }
            let cap = max_card.max(1);
            let en = plan[crate::encoded_order::schema::WIDTH];
            let p = self.static_words(plan);
            let s = self.expr(set)?;
            let k = self.fresh();
            return Ok(format!("{pad}{{ const uint64_t *S{k} = {s}; uint64_t I{k}[{cap}]; tlx_order_indices({p}, S{k}, I{k});\n{pad}for (uint64_t i{k} = 0; i{k} < S{k}[0]; i{k}++) {{ const uint64_t *{t} = S{k} + 1 + I{k}[i{k}] * {en};\n{body}{pad}}} }}\n"));
        }
        if let ExprKind::ConstElems { elem, words, count } = &*set.kind {
            let n = self.words(*elem);
            let arr = self.static_words(words);
            let k = self.fresh();
            return Ok(format!(
                "{pad}for (uint32_t c{k} = 0; c{k} < {count}; c{k}++) {{ const uint64_t *{t} = {arr} + c{k} * {n};\n{body}{pad}}}\n"
            ));
        }
        if let ExprKind::IntRange(lo, hi) = &*set.kind {
            let (lo, hi) = (self.int_expr(lo)?, self.int_expr(hi)?);
            return Ok(format!("{pad}for (int64_t {t} = {lo}, {t}_hi = {hi}; {t} <= {t}_hi; {t}++) {{\n{body}{pad}}}\n"));
        }
        if let ExprKind::Subsets(x) = &*set.kind {
            // Ranks of the elements, then each k-combination of them in
            // lexicographic order, for k = 0..n.
            let Ty::Enc(sid) = x.ty else { return no("subsets of a boxed set") };
            let n = self.words(sid);
            let s = self.expr(x)?;
            let k = self.fresh();
            let mut out = String::new();
            writeln!(out, "{pad}{{ const uint64_t *ssS{k} = {s}; uint32_t ssRK{k}[64]; uint32_t ssn{k} = 0;").unwrap();
            writeln!(out, "{pad}for (uint32_t ssw{k} = 0; ssw{k} < {n}; ssw{k}++) {{ uint64_t ssB{k} = ssS{k}[ssw{k}]; while (ssB{k}) {{ if (ssn{k} == 24) return TLX_ERR; ssRK{k}[ssn{k}++] = ssw{k} * 64 + (uint32_t)__builtin_ctzll(ssB{k}); ssB{k} &= ssB{k} - 1; }} }}").unwrap();
            writeln!(out, "{pad}for (uint32_t ssk{k} = 0; ssk{k} <= ssn{k}; ssk{k}++) {{ uint32_t ssI{k}[64]; for (uint32_t ssj{k} = 0; ssj{k} < ssk{k}; ssj{k}++) ssI{k}[ssj{k}] = ssj{k};").unwrap();
            writeln!(out, "{pad}for (;;) {{ uint64_t ssT{k}[{n}] = {{0}}; for (uint32_t ssj{k} = 0; ssj{k} < ssk{k}; ssj{k}++) ssT{k}[ssRK{k}[ssI{k}[ssj{k}]] / 64] |= 1ULL << (ssRK{k}[ssI{k}[ssj{k}]] % 64);").unwrap();
            writeln!(out, "{pad}  const uint64_t *{t} = ssT{k};").unwrap();
            out.push_str(body);
            writeln!(out, "{pad}  uint32_t ssi{k} = ssk{k}; while (ssi{k} > 0 && ssI{k}[ssi{k} - 1] == ssn{k} - ssk{k} + ssi{k} - 1) ssi{k}--; if (ssi{k} == 0) break;").unwrap();
            writeln!(out, "{pad}  ssI{k}[ssi{k} - 1]++; for (uint32_t ssj{k} = ssi{k}; ssj{k} < ssk{k}; ssj{k}++) ssI{k}[ssj{k}] = ssI{k}[ssj{k} - 1] + 1; }} }} }}").unwrap();
            return Ok(out);
        }
        let Ty::Enc(sid) = set.ty else { return no("iteration over a boxed set") };
        let Shape::Set { elem, .. } = self.ty.shape(sid).clone() else { return no("iteration over a non-set") };
        let s = self.expr(set)?;
        let k = self.fresh();
        let mut out = String::new();
        if bitset_universe(&elem).is_some() {
            let (kk, digits) = self.unrank_code(&elem, k)?;
            let n = self.words(sid);
            let mask = self.mask_of(&elem, n, bind, pred, k);
            writeln!(out, "{pad}{{ const uint64_t *S{k} = {s};").unwrap();
            writeln!(out, "{pad}for (uint32_t w{k} = 0; w{k} < {n}; w{k}++) {{ uint64_t B{k} = S{k}[w{k}]{mask};").unwrap();
            writeln!(out, "{pad}while (B{k}) {{ uint64_t q{k} = w{k} * 64 + (uint64_t)__builtin_ctzll(B{k}); uint64_t R{k}[{kk}]; {digits}B{k} &= B{k} - 1;").unwrap();
            writeln!(out, "{pad}  const uint64_t *{t} = R{k};").unwrap();
            out.push_str(body);
            writeln!(out, "{pad}}} }} }}").unwrap();
        } else {
            let en = self.words(self.find_sid(&elem)?);
            writeln!(out, "{pad}{{ const uint64_t *S{k} = {s};").unwrap();
            writeln!(out, "{pad}for (uint64_t i{k} = 0; i{k} < S{k}[0]; i{k}++) {{").unwrap();
            writeln!(out, "{pad}  const uint64_t *{t} = S{k} + 1 + i{k} * {en};").unwrap();
            out.push_str(body);
            writeln!(out, "{pad}}} }}").unwrap();
        }
        Ok(out)
    }

    /// ` & <mask>[w{k}]` restricting the loop over the `n`-word bitset of
    /// `elem` elements to the ranks that can pass `pred` (`rankmask`), or
    /// nothing (`k`: the loop's number, see the variable `w{k}`).
    pub(super) fn mask_of(&mut self, elem: &Shape, n: usize, bind: Temp, pred: Option<&Expr>, k: usize) -> String {
        let Some(m) = pred.and_then(|p| crate::rankmask::rank_mask(self.ty, elem, n, bind, p)) else { return String::new() };
        let name = self.static_words(&m);
        format!(" & {name}[w{k}]")
    }

    /// C code computing, from a rank in `q{k}`, the element's encoding in a
    /// local array `R{k}` (its size is returned): scalars are their rank,
    /// flat products their digits (mixed radix), unions of those an arm
    /// index followed by the arm's digits (zero-padded).
    pub(super) fn unrank_code(&mut self, elem: &Shape, k: usize) -> R<(usize, String)> {
        let digits_into = |shape: &Shape, radices: &[u64], first: usize| -> String {
            let mut d = String::new();
            let parts: Option<Vec<&Shape>> = match shape {
                Shape::Tuple(es) => Some(es.iter().collect()),
                Shape::Record(fs) => Some(fs.iter().map(|(_, f)| f).collect()),
                _ => None,
            };
            let fl = FieldLayout::of_shape(shape);
            for (i, c) in radices.iter().enumerate().rev() {
                match (&fl, &parts) {
                    (Some(fl), Some(ps)) => {
                        if tlx_layout::layout::words(ps[i]) == 0 {
                            write!(d, "q{k} /= {c}ULL; ").unwrap();
                        } else {
                            match fl.locs[i] {
                                FieldLoc::Words(w) => {
                                    write!(d, "R{k}[{}] = q{k} % {c}ULL; q{k} /= {c}ULL; ", first + w).unwrap();
                                }
                                FieldLoc::Bits(pos) => {
                                    write!(
                                        d,
                                        "tlx_bset(R{k}, {}, {}, {}, q{k} % {c}ULL); q{k} /= {c}ULL; ",
                                        first + pos.word,
                                        pos.shift,
                                        pos.bits
                                    )
                                    .unwrap();
                                }
                            }
                        }
                    }
                    _ => {
                        if tlx_layout::layout::words(shape) > 0 {
                            write!(d, "R{k}[{}] = q{k} % {c}ULL; q{k} /= {c}ULL; ", first + i).unwrap();
                        } else {
                            write!(d, "q{k} /= {c}ULL; ").unwrap();
                        }
                    }
                }
            }
            d
        };
        if elem.is_scalar() {
            let w = tlx_layout::layout::words(elem).max(1);
            return Ok((w, digits_into(elem, &[elem.cardinality().unwrap_or(1)], 0)));
        }
        if let Some(r) = crate::lower::flat_radices(elem) {
            let w = tlx_layout::layout::words(elem).max(1);
            let mut d = format!("memset(R{k}, 0, sizeof R{k}); ");
            d.push_str(&digits_into(elem, &r, 0));
            return Ok((w, d));
        }
        if let Some(arms) = crate::lower::union_radices(elem) {
            let Shape::Union(arm_shapes) = elem else { unreachable!() };
            let w = self.words(self.find_sid(elem)?).max(1);
            let mut d = format!("memset(R{k}, 0, sizeof R{k}); ");
            for (i, r) in arms.iter().enumerate() {
                let card: u64 = r.iter().product();
                write!(d, "if (q{k} < {card}ULL) {{ R{k}[0] = {i}; {}}} else {{ q{k} -= {card}ULL; ", digits_into(&arm_shapes[i], r, 1))
                    .unwrap();
            }
            d.push_str(&"} ".repeat(arms.len()));
            return Ok((w, d));
        }
        if crate::lower::rankable(elem) {
            // Products and unions of those: digits recursively, each part
            // from its own rank.
            let w = self.words(self.find_sid(elem)?).max(1);
            let mut d = format!("memset(R{k}, 0, sizeof R{k}); ");
            let mut fresh = 0;
            self.unrank_nested(elem, &format!("q{k}"), 0, k, &mut fresh, &mut d)?;
            return Ok((w, d));
        }
        no("bitset of composite elements")
    }

    /// C code writing the encoding of the value of rank `q` (a variable it
    /// may modify) of rankable shape `s` into `R{k}[off..]`.
    fn unrank_nested(&mut self, s: &Shape, q: &str, off: usize, k: usize, fresh: &mut usize, d: &mut String) -> R<()> {
        let var = |fresh: &mut usize| {
            *fresh += 1;
            format!("q{k}_{fresh}")
        };
        match s {
            Shape::Int { .. } | Shape::Atom(_) | Shape::Bool => {
                if tlx_layout::layout::words(s) > 0 {
                    write!(d, "R{k}[{off}] = {q}; ").unwrap();
                }
            }
            // A set whose rank is its bitset (none: a set over an empty
            // universe has no words).
            Shape::Set { .. } if crate::lower::word_ranked_set(s) => {
                if self.words(self.find_sid(s)?) > 0 {
                    write!(d, "R{k}[{off}] = {q}; ").unwrap();
                }
            }
            Shape::Tuple(_) | Shape::Record(_) => {
                let parts: Vec<Shape> = match s {
                    Shape::Tuple(es) => es.to_vec(),
                    Shape::Record(fs) => fs.iter().map(|(_, f)| f.clone()).collect(),
                    _ => unreachable!(),
                };
                let fl = FieldLayout::of_shape(s).expect("Tuple or Record");
                for (p, loc) in parts.iter().zip(fl.locs.iter().copied()).rev() {
                    let Some(c) = p.cardinality() else { return no("unranked part without cardinality") };
                    let v = var(fresh);
                    write!(d, "uint64_t {v} = {q} % {c}ULL; {q} /= {c}ULL; ").unwrap();
                    match loc {
                        FieldLoc::Bits(pos) => {
                            write!(d, "tlx_bset(R{k}, {}, {}, {}, {v}); ", off + pos.word, pos.shift, pos.bits).unwrap();
                        }
                        FieldLoc::Words(w) => {
                            if tlx_layout::layout::words(p) > 0 {
                                self.unrank_nested(p, &v, off + w, k, fresh, d)?;
                            }
                        }
                    }
                }
            }
            Shape::Union(arms) => {
                for (i, a) in arms.iter().enumerate() {
                    let Some(c) = a.cardinality() else { return no("unranked arm without cardinality") };
                    write!(d, "if ({q} < {c}ULL) {{ R{k}[{off}] = {i}; ").unwrap();
                    self.unrank_nested(a, q, off + 1, k, fresh, d)?;
                    write!(d, "}} else {{ {q} -= {c}ULL; ").unwrap();
                }
                d.push_str(&"} ".repeat(arms.len()));
            }
            _ => return no("bitset of composite elements"),
        }
        Ok(())
    }
}
