//! Expression transfer rules: the shape of every expression kind, the
//! binders they introduce, and the constant reads they record as atoms.

use std::collections::BTreeMap;
use std::sync::Arc;

use tlx_sema::hir::*;
use tlx_value::Value;

use super::super::shape::{self, Lit, OpVal, Sh, ALL};
use super::{choices::unique_choice, Analyzer, Arg, Atom, AtomKey};
use crate::env::Env;
use crate::eval::Ctx;
use crate::interp::ConstVal;

impl<'a> Analyzer<'a> {
    pub(super) fn expr(&mut self, e: &Expr) -> Sh {
        self.steps += 1;
        if self.steps > super::MAX_STEPS {
            self.overflow = true;
        }
        if self.overflow {
            return Sh::any(ALL);
        }
        match &*e.kind {
            ExprKind::Num(_) | ExprKind::Decimal(_) | ExprKind::Str(_) | ExprKind::Bool(_) => Sh::plain(),
            ExprKind::Var(v) => self.vars[v.idx()].clone(),
            ExprKind::InstVar { subst, .. } => self.expr(subst),
            ExprKind::Const(c) => self.constant(*c, e.span),
            ExprKind::Local(l) => match self.local(*l) {
                Some(a) => a.sh.clone(),
                None => Sh::any(ALL),
            },
            ExprKind::Apply { op, args } => self.apply(op, args, e.span),
            ExprKind::Builtin { op, args } => self.builtin_expr(*op, args, e.span),
            ExprKind::OpArg(r) => self.op_ref(r, e.span),
            ExprKind::Lambda { .. } => Sh::op(OpVal::Lambda(e.clone())),
            ExprKind::And(es) | ExprKind::Or(es) => self.and_or(es),
            ExprKind::Quant { bounds, body, .. } => self.quant(bounds, body),
            ExprKind::QuantUnbounded { vars, body, .. } | ExprKind::TemporalQuant { vars, body, .. } => self.quant_unbounded(vars, body),
            ExprKind::Choose { vars, set, body } => self.choose(e, vars, set, body),
            ExprKind::If { cond, then, els } => self.ite(cond, then, els),
            ExprKind::Case { arms, other } => self.case(arms, other),
            ExprKind::Let { body, .. } => self.expr(body),
            ExprKind::SetEnum(es) => self.set_enum(es),
            ExprKind::SetFilter { bound, pred } => self.set_filter(bound, pred),
            ExprKind::SetMap { expr, bounds } => self.set_map(expr, bounds),
            ExprKind::Tuple(es) => Sh::tup(es.iter().map(|x| self.expr(x)).collect()),
            ExprKind::FnConstruct { bounds, body } => self.fn_construct(bounds, body),
            ExprKind::FnApp { func, args } => self.fn_app(func, args),
            ExprKind::FnSet { domain, range } => self.fn_set(domain, range),
            ExprKind::Record(fs) => self.record(fs),
            ExprKind::RecordSet(fs) => self.record_set(fs),
            ExprKind::Field { record, field } => self.expr(record).field(field),
            ExprKind::Except { base, updates } => self.except(base, updates),
            ExprKind::At => self.at.last().cloned().unwrap_or_else(|| Sh::any(ALL)),
            ExprKind::BoxAction { action, sub } | ExprKind::AngleAction { action, sub } => self.action(action, sub),
            // Fairness only concerns liveness, which auto symmetry leaves out.
            ExprKind::Fairness { .. } => Sh::plain(),
        }
    }

    /// `And`/`Or`: analyze every operand; the result does not depend on the
    /// order of the model values.
    fn and_or(&mut self, es: &[Expr]) -> Sh {
        for x in es {
            self.expr(x);
        }
        Sh::plain()
    }

    /// A bounded quantifier: bind its variables for the body.
    fn quant(&mut self, bounds: &[Bound], body: &Expr) -> Sh {
        let mark = self.locals.len();
        for b in bounds {
            self.bind(b);
        }
        self.expr(body);
        self.locals.truncate(mark);
        Sh::plain()
    }

    /// An unbounded or temporal quantifier: every variable may hold
    /// anything.
    fn quant_unbounded(&mut self, vars: &[LocalId], body: &Expr) -> Sh {
        let mark = self.locals.len();
        for v in vars {
            self.locals.push((*v, Arg::of(Sh::any(ALL))));
        }
        self.expr(body);
        self.locals.truncate(mark);
        Sh::plain()
    }

    /// `CHOOSE`: the result is the projected element; a candidate set with
    /// more than one element that no fold makes unique breaks the symmetry.
    fn choose(&mut self, e: &Expr, vars: &BoundVars, set: &Option<Expr>, body: &Expr) -> Sh {
        let mark = self.locals.len();
        let result = match set {
            Some(set) => {
                let el = self.expr(set).elems();
                self.bind_vars(vars, &el);
                self.expr(body);
                let m = el.mask();
                if m != 0 && !unique_choice(vars, set, body) && !self.folds.contains(&(Arc::as_ptr(&e.kind) as usize)) {
                    self.breaker(m, "CHOOSE", e.span);
                }
                el
            }
            None => {
                for v in vars.locals() {
                    self.locals.push((*v, Arg::of(Sh::any(ALL))));
                }
                self.expr(body);
                // (Evaluating an unbounded CHOOSE is an error.)
                Sh::default()
            }
        };
        self.locals.truncate(mark);
        result
    }

    /// `IF`/`THEN`/`ELSE`: the join of both branches.
    fn ite(&mut self, cond: &Expr, then: &Expr, els: &Expr) -> Sh {
        self.expr(cond);
        let a = self.expr(then);
        a.join(&self.expr(els))
    }

    /// `CASE`: the join of every arm and the `OTHER` branch.
    fn case(&mut self, arms: &[(Expr, Expr)], other: &Option<Expr>) -> Sh {
        let mut r = Sh::default();
        for (g, v) in arms {
            self.expr(g);
            r = r.join(&self.expr(v));
        }
        if let Some(o) = other {
            r = r.join(&self.expr(o));
        }
        r
    }

    /// A set enumeration: the join of its elements.
    fn set_enum(&mut self, es: &[Expr]) -> Sh {
        let mut r = Sh::default();
        for x in es {
            r = r.join(&self.expr(x));
        }
        Sh::set(r)
    }

    /// `{ x \in S : p }`: the shape of `S`'s elements, bound for `p`.
    fn set_filter(&mut self, bound: &Bound, pred: &Expr) -> Sh {
        let mark = self.locals.len();
        let el = self.bind(bound);
        self.expr(pred);
        self.locals.truncate(mark);
        Sh::set(el)
    }

    /// `{ e : b }`: `e`'s shape over the bounds' elements.
    fn set_map(&mut self, expr: &Expr, bounds: &[Bound]) -> Sh {
        let mark = self.locals.len();
        for b in bounds {
            self.bind(b);
        }
        let r = self.expr(expr);
        self.locals.truncate(mark);
        Sh::set(r)
    }

    /// `[ b |-> e ]`: a function over the bounds' domain with `e`'s range.
    fn fn_construct(&mut self, bounds: &[Bound], body: &Expr) -> Sh {
        let mark = self.locals.len();
        let dom = self.bind_domain(bounds);
        let r = self.expr(body);
        self.locals.truncate(mark);
        Sh::fcn(dom, r)
    }

    /// `f[a]`: indexing a function (a tuple index, otherwise its range).
    fn fn_app(&mut self, func: &Expr, args: &[Expr]) -> Sh {
        let f = self.expr(func);
        for a in args {
            self.expr(a);
        }
        if args.len() == 1 {
            f.apply(Lit::of(&args[0]).as_ref())
        } else {
            f.range()
        }
    }

    /// `[ D -> R ]`: the set of functions from `D` to `R`.
    fn fn_set(&mut self, domain: &Expr, range: &Expr) -> Sh {
        let d = self.expr(domain).elems();
        let r = self.expr(range).elems();
        Sh::set(Sh::fcn(d, r))
    }

    /// `[ a |-> e, .. ]`: a record whose fields take the fields' shapes.
    fn record(&mut self, fs: &[(Arc<str>, Expr)]) -> Sh {
        let mut m = BTreeMap::new();
        for (k, x) in fs {
            let s = self.expr(x);
            m.insert(k.clone(), s);
        }
        Sh::rec(m)
    }

    /// `[ a : S, .. ]`: the set of records over the fields' elements.
    fn record_set(&mut self, fs: &[(Arc<str>, Expr)]) -> Sh {
        let mut m = BTreeMap::new();
        for (k, x) in fs {
            let s = self.expr(x).elems();
            m.insert(k.clone(), s);
        }
        Sh::set(Sh::rec(m))
    }

    /// `[ f EXCEPT !.k = v ]`: apply the updates to the base value.
    fn except(&mut self, base: &Expr, updates: &[(Vec<ExceptKey>, Expr)]) -> Sh {
        let mut b = self.expr(base);
        for (keys, v) in updates {
            b = self.update(&b, keys, v);
        }
        b
    }

    /// `[A]_v` / `<A>_v`: an action and its subscript.
    fn action(&mut self, action: &Expr, sub: &Expr) -> Sh {
        self.expr(action);
        self.expr(sub);
        Sh::plain()
    }

    /// Bind the variables of `b` to the elements of its set; their shape.
    fn bind(&mut self, b: &Bound) -> Sh {
        let el = self.expr(&b.set).elems();
        self.bind_vars(&b.vars, &el);
        el
    }

    fn bind_vars(&mut self, vars: &BoundVars, el: &Sh) {
        match vars {
            BoundVars::Many(ids) => {
                for id in ids {
                    self.locals.push((*id, Arg::of(el.clone())));
                }
            }
            BoundVars::Tuple(ids) => {
                for (i, id) in ids.iter().enumerate() {
                    self.locals.push((*id, Arg::of(el.index(i as i128 + 1))));
                }
            }
        }
    }

    /// Bind the variables of a function's bounds; the shape of its domain
    /// elements (tuples for several variables).
    pub(super) fn bind_domain(&mut self, bounds: &[Bound]) -> Sh {
        let mut parts = Vec::new();
        for b in bounds {
            let el = self.bind(b);
            match &b.vars {
                BoundVars::Many(ids) => parts.extend(ids.iter().map(|_| el.clone())),
                BoundVars::Tuple(_) => parts.push(el),
            }
        }
        if parts.len() == 1 {
            parts.pop().unwrap()
        } else {
            Sh::tup(parts)
        }
    }

    fn update(&mut self, b: &Sh, keys: &[ExceptKey], v: &Expr) -> Sh {
        let Some((k, rest)) = keys.split_first() else {
            self.at.push(b.clone());
            let r = self.expr(v);
            self.at.pop();
            return r;
        };
        match k {
            ExceptKey::Field(f) => {
                let lit = Lit::Str(f.clone());
                let inner = self.update(&b.field(f), rest, v);
                b.with_entry(&Sh::plain(), Some(&lit), &inner)
            }
            ExceptKey::Index(ix) => {
                let mut ks: Vec<Sh> = ix.iter().map(|x| self.expr(x)).collect();
                let (ksh, lit) = if ks.len() == 1 { (ks.pop().unwrap(), Lit::of(&ix[0])) } else { (Sh::tup(ks), None) };
                let inner = self.update(&b.apply(lit.as_ref()), rest, v);
                b.with_entry(&ksh, lit.as_ref(), &inner)
            }
        }
    }

    fn constant(&mut self, c: ConstId, span: Span) -> Sh {
        let ip = self.ip;
        let name = &ip.prog.consts[c.idx()].name;
        match &ip.consts[c.idx()] {
            Some(ConstVal::Value(v)) => self.atom(AtomKey::Const(c), v, name, span),
            Some(ConstVal::Def(d)) => self.apply_def(*d, Vec::new(), span),
            Some(ConstVal::Op(r)) => self.apply_ref(r, Vec::new(), span),
            Some(ConstVal::Table(rows)) => self.table(c, rows, span),
            None => {
                self.breaker(ALL, format!("the constant {name} without a value"), span);
                Sh::any(ALL)
            }
        }
    }

    /// An operator constant given by its values (`F(1) = a` in the cfg):
    /// an atom, the set of its rows.
    pub(super) fn table(&mut self, c: ConstId, rows: &[(Vec<Value>, Value)], span: Span) -> Sh {
        let name = self.ip.prog.consts[c.idx()].name.to_string();
        let rows: Vec<Value> = rows.iter().map(|(a, v)| Value::tuple(vec![Value::tuple(a.clone()), v.clone()])).collect();
        match Value::set_from(rows) {
            Ok(set) => self.atom(AtomKey::Const(c), &set, &name, span).elems().index(2),
            Err(_) => {
                self.breaker(ALL, format!("the operator constant {name}"), span);
                Sh::any(ALL)
            }
        }
    }

    pub(super) fn atom(&mut self, key: AtomKey, v: &Value, name: &str, span: Span) -> Sh {
        let sh = match shape::of_value(v, self.mask_of) {
            Some(sh) => sh,
            None => {
                self.breaker(ALL, format!("the value of {name}"), span);
                return Sh::any(ALL);
            }
        };
        if sh.mask() != 0 && self.atom_keys.insert(key) {
            self.atoms.push(Atom { value: v.clone(), name: name.to_string(), at: None });
        }
        sh
    }

    /// A 0-ary constant-level definition: an atom, its value (`None` if
    /// it cannot be evaluated or shaped: then its body is analyzed).
    pub(super) fn const_def(&mut self, d: DefId) -> Option<Sh> {
        if let Some(r) = self.const_defs.get(&d) {
            // (Recorded as an atom when first evaluated.)
            return r.clone();
        }
        let ip = self.ip;
        let def = &ip.prog.defs[d.idx()];
        let e = Expr::new(ExprKind::Apply { op: OpRef::Def(d), args: Vec::new() }, def.span);
        let r = match ip.eval(&e, &Env::default(), &Ctx::NONE) {
            Ok(v) => match shape::of_value(&v, self.mask_of) {
                Some(sh) => {
                    if sh.mask() != 0 && self.atom_keys.insert(AtomKey::Def(d)) {
                        self.atoms.push(Atom { value: v, name: def.name.to_string(), at: Some(def.span) });
                    }
                    Some(sh)
                }
                None => None,
            },
            Err(_) => None,
        };
        self.const_defs.insert(d, r.clone());
        r
    }

    fn op_ref(&mut self, r: &OpRef, span: Span) -> Sh {
        let ip = self.ip;
        match r {
            OpRef::Def(d) => Sh::op(OpVal::Def(ip.redirect_def(*d))),
            OpRef::Builtin(b) => match ip.builtin_override(*b) {
                Some(d) => Sh::op(OpVal::Def(ip.redirect_def(d))),
                None => Sh::op(OpVal::Builtin(*b)),
            },
            OpRef::Param(l) => self.local(*l).map(|a| a.sh.clone()).unwrap_or_else(|| Sh::any(ALL)),
            OpRef::Const(c) => match &ip.consts[c.idx()] {
                Some(ConstVal::Op(r)) => self.op_ref(r, span),
                Some(ConstVal::Def(d)) => Sh::op(OpVal::Def(ip.redirect_def(*d))),
                _ => {
                    let name = &ip.prog.consts[c.idx()].name;
                    self.breaker(ALL, format!("the operator constant {name} passed as an argument"), span);
                    Sh::any(ALL)
                }
            },
        }
    }
}
