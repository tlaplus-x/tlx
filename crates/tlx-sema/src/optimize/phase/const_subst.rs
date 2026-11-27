//! `.cfg` substitution resolution (constants and definition overrides), the shared
//! redirect table, the canonical/syntactic HIR writers, and the Lean obligations
//! that connect declared substitutions to the generated model.

use std::collections::HashMap;

use tlx_front::cfg::{Config, ConstBinding};

use crate::hir::{Bound, BoundVars, ConstId, DefId, DefKind, ExceptKey, Expr, ExprKind, LocalId, OpRef, RootSymbol, Span};

const MAX_REDIRECT_WORK: usize = 100_000;
use crate::{builtins::Builtin as B, Program};

use super::cert::OpenCert;

/// Resolved target of a zero-arity `CONSTANT C <- target` `.cfg` substitution.
#[derive(Clone, Copy, Debug)]
pub(in crate::optimize::phase) enum ConstSubstTarget {
    PureBuiltin(B, Span),
    Def(DefId),
    Const(ConstId),
}

/// The `.cfg` definition overrides a certified normalization must apply,
/// mirroring `bind_cfg` (`tlx-eval/src/interp/cfg.rs`): `F <- G` replaces every
/// definition SANY represents by `F`'s node (the copies of an `INSTANCE`d
/// module, but not an `I!F` entry node of its own, docs/compat.md D-23).
///
/// Every value is a *terminal* replacement: chains are followed the way
/// `Interp::redirect_def` follows them, cycles are rejected, and the terminal
/// definition's arity must equal the replaced definition's, so a call of the
/// replaced operator can be spliced without changing arity. Returns `None` for
/// any binding the certified path refuses: module-scoped overrides, unresolved
/// symbols, arity mismatches, redirect cycles, or impure replacement bodies.
pub(crate) struct CfgRedirects {
    /// Root definitions replaced by `F <- G` (all copies SANY shares).
    pub defs: HashMap<DefId, DefId>,
    /// Builtin operators replaced through the root definition that carries
    /// them. HIR references to such an operator are `ExprKind::Builtin` /
    /// `OpRef::Builtin` nodes without a definition id, so the replacement has
    /// to be applied by operator as well as by node.
    pub builtins: HashMap<crate::builtins::Builtin, (DefId, DefId)>,
}

/// DefIds called by an HIR expression (definitions, `LET` bodies, and operator
/// arguments). Used to reject recursive replacement targets: the certified
/// lowering never keeps a recursive override in the rule-IR model.
fn collect_def_calls(e: &Expr, f: &mut impl FnMut(DefId)) {
    match &*e.kind {
        ExprKind::Apply { op: OpRef::Def(d), .. } => f(*d),
        ExprKind::OpArg(OpRef::Def(d)) => f(*d),
        ExprKind::Let { defs, .. } => defs.iter().for_each(|d| f(*d)),
        _ => {}
    }
    crate::visit::children(e, &mut |c| collect_def_calls(c, f));
}

/// Whether `root` is (transitively) recursive. Unresolved bodies and an
/// exhausted work budget count as recursive, so the caller fails closed.
fn def_is_recursive(program: &Program, root: DefId) -> bool {
    let mut seen = std::collections::HashSet::new();
    let mut stack = vec![root];
    let mut work = 10_000usize;
    while let Some(d) = stack.pop() {
        if work == 0 {
            return true;
        }
        work -= 1;
        let def = match &program.defs[d.idx()].kind {
            DefKind::Op(b) => b,
            DefKind::Fn { bounds, body } => {
                for b in bounds {
                    let mut found = false;
                    collect_def_calls(&b.set, &mut |c| {
                        if c == root {
                            found = true;
                        }
                    });
                    if found {
                        return true;
                    }
                }
                body
            }
            DefKind::Pending => return true,
        };
        let mut callees = Vec::new();
        collect_def_calls(def, &mut |c| callees.push(c));
        for c in callees {
            if c == root {
                return true;
            }
            if seen.insert(c) {
                stack.push(c);
            }
        }
    }
    false
}

pub(crate) fn cfg_def_redirects(program: &Program, cfg: &Config) -> Option<CfgRedirects> {
    use crate::builtins::Effect;
    let mut raw: HashMap<DefId, DefId> = HashMap::new();
    let mut builtin_raw: HashMap<crate::builtins::Builtin, (DefId, DefId)> = HashMap::new();
    for b in &cfg.constants {
        let ConstBinding::Subst { name, op, module } = b else { continue };
        if module.is_some() {
            return None;
        }
        let Some(RootSymbol::Def(lhs)) = program.lookup_resolved_root(name) else { continue };
        let Some(RootSymbol::Def(target)) = program.lookup_resolved_root(op) else { return None };
        if let Some(op) = program.defs[lhs.idx()].builtin {
            if builtin_raw.insert(op, (lhs, target)).is_some() {
                return None;
            }
        }
        for d in program.resolved_def_copies(lhs)? {
            match raw.insert(d, target) {
                // Two bindings of the same node must agree (`last wins` would
                // hide the earlier body from this analysis).
                Some(prev) if prev != target => return None,
                _ => {}
            }
        }
    }
    let mut out: HashMap<DefId, DefId> = HashMap::with_capacity(raw.len());
    for &lhs in raw.keys() {
        let mut cur = lhs;
        let mut seen = vec![lhs];
        while let Some(&next) = raw.get(&cur) {
            if seen.contains(&next) {
                return None;
            }
            seen.push(next);
            cur = next;
        }
        let terminal = &program.defs[cur.idx()];
        if terminal.params.len() != program.defs[lhs.idx()].params.len() {
            return None;
        }
        if let Some(op) = terminal.builtin {
            if op.metadata().effect != Effect::Pure {
                return None;
            }
        }
        out.insert(lhs, cur);
    }
    let mut budget = MAX_REDIRECT_WORK;
    if !out.values().all(|&target| super::sym_totality::def_is_pure(program, cfg, &out, target, &mut budget)) {
        return None;
    }
    for (op, &(_, target)) in &builtin_raw {
        let arity = op.metadata().arity;
        // A variadic builtin, or one used at a different arity, cannot be
        // spliced for a call site without changing its meaning.
        if arity < 0 || program.defs[target.idx()].params.len() != arity as usize {
            return None;
        }
        if op.metadata().effect != Effect::Pure {
            return None;
        }
    }
    if out.values().any(|&target| def_is_recursive(program, target)) {
        return None;
    }
    Some(CfgRedirects { defs: out, builtins: builtin_raw })
}

/// Resolve the RHS symbol name of a `.cfg` `<-` substitution into something a
/// normalizer can splice: a pure builtin, a non-`LET` root definition of any
/// arity, or a zero-arity constant. Arity agreement with the replaced symbol is
/// the caller's check; an operator itself is not a value here.
pub(in crate::optimize::phase) fn resolve_override_name(program: &Program, target: &str) -> Option<ConstSubstTarget> {
    match program.lookup_resolved_root(target)? {
        RootSymbol::Def(did) => {
            let d = &program.defs[did.idx()];
            if program.def_is_let(did) {
                return None;
            }
            if let Some(op) = d.builtin {
                (op.metadata().effect == crate::builtins::Effect::Pure).then_some(ConstSubstTarget::PureBuiltin(op, d.span))
            } else {
                Some(ConstSubstTarget::Def(did))
            }
        }
        RootSymbol::Const(other) if program.consts[other.idx()].arity == 0 => Some(ConstSubstTarget::Const(other)),
        _ => None,
    }
}

/// Resolve a `.cfg` substitution RHS symbol name into a pure zero-arity builtin,
/// non-`LET` zero-arity root definition, or zero-arity constant.
pub(in crate::optimize::phase) fn resolve_const_subst_name(program: &Program, target: &str) -> Option<ConstSubstTarget> {
    match resolve_override_name(program, target)? {
        ConstSubstTarget::Def(did) if !program.defs[did.idx()].params.is_empty() => None,
        target => Some(target),
    }
}

/// One `.cfg` definition or parameterized-constant override the normalizer
/// actually applied while lowering: the replaced root name, its configured
/// replacement name, the concrete argument tuple, the canonical HIR of the
/// expansion (checked against the declaration), and the same expansion printed
/// with local ids verbatim (so it can be located inside a normalized model
/// formula and connected to the generated system).
pub(in crate::optimize::phase) struct OverrideObligations<'a> {
    pub applied: &'a [AppliedOverride],
    pub model_hirs: &'a [String],
}

pub(in crate::optimize::phase) struct AppliedOverride {
    pub name: String,
    pub target: String,
    pub args: Vec<Expr>,
    pub applied: String,
    pub applied_syntax: String,
}

/// Resolve a zero-arity constant's last `.cfg` substitution target.
pub(in crate::optimize::phase) fn resolve_const_subst_target(program: &Program, cfg: &Config, c: ConstId) -> Option<ConstSubstTarget> {
    if program.consts[c.idx()].arity != 0 {
        return None;
    }
    let target = cfg.last_constant_subst(&program.consts[c.idx()].name)?;
    resolve_const_subst_name(program, target)
}

/// Follow a chain of zero-arity `CONSTANT C <- C2 <- ...` substitutions until a
/// terminal `PureBuiltin`, `Def`, or un-substituted `Const`, rejecting cycles.
pub(in crate::optimize::phase) fn resolve_const_subst_chain(
    program: &Program,
    cfg: &Config,
    c: ConstId,
) -> Option<(Vec<ConstId>, ConstSubstTarget)> {
    let mut seen = vec![c];
    let mut cur = c;
    loop {
        match resolve_const_subst_target(program, cfg, cur)? {
            ConstSubstTarget::Const(other) => {
                if seen.contains(&other) {
                    return None;
                }
                seen.push(other);
                if cfg.last_constant_subst(&program.consts[other.idx()].name).is_some() {
                    cur = other;
                } else {
                    return Some((seen, ConstSubstTarget::Const(other)));
                }
            }
            terminal => return Some((seen, terminal)),
        }
    }
}

const MAX_CANON_WORK: usize = 100_000;
const MAX_CANON_BYTES: usize = 1_000_000;
const MAX_CANON_DEPTH: usize = 128;
const MAX_CERT_CONST_SUBSTS: usize = 1024;

struct CanonWriter<'a> {
    program: &'a Program,
    next_id: usize,
    work: usize,
    max_bytes: usize,
    out: String,
    /// Print local ids verbatim instead of alpha-renaming them. A normalized
    /// model formula then contains the exact text of an expansion recorded at
    /// an inner use site (same local ids), so a `++` decomposition can be
    /// checked by `rfl`.
    syntactic: bool,
}

impl<'a> CanonWriter<'a> {
    fn push(&mut self, s: &str) -> Option<()> {
        if self.out.len().checked_add(s.len())? > self.max_bytes {
            return None;
        }
        self.out.push_str(s);
        Some(())
    }

    fn push_char(&mut self, ch: char) -> Option<()> {
        if self.out.len().checked_add(ch.len_utf8())? > self.max_bytes {
            return None;
        }
        self.out.push(ch);
        Some(())
    }

    fn register_locals(&mut self, ls: &[LocalId], locals: &mut std::collections::HashMap<LocalId, usize>) -> Option<()> {
        for (j, l) in ls.iter().enumerate() {
            if j > 0 {
                self.push_char(',')?;
            }
            if self.syntactic {
                self.push(&format!("Local({})", l.0))?;
                continue;
            }
            let id = self.next_id;
            self.next_id += 1;
            locals.insert(*l, id);
            self.push(&format!("L{id}"))?;
        }
        Some(())
    }

    fn fmt_opref(&mut self, op: &OpRef) -> Option<()> {
        match op {
            OpRef::Def(d) => self.push(&format!("Def({})", d.0)),
            OpRef::Const(c) => self.push(&format!("Const({})", c.0)),
            OpRef::Param(l) => self.push(&format!("Param({})", l.0)),
            OpRef::Builtin(b) => self.push(&format!("Builtin({b:?})")),
        }
    }

    fn fmt_opt_expr(&mut self, e: &Expr, locals: &mut std::collections::HashMap<LocalId, usize>, depth: usize) -> Option<()> {
        self.fmt_expr(e, locals, depth)
    }

    fn fmt_bound_vars(&mut self, vars: &BoundVars, locals: &mut std::collections::HashMap<LocalId, usize>) -> Option<()> {
        let (tag, ls) = match vars {
            BoundVars::Many(ls) => ("Many(", ls.as_slice()),
            BoundVars::Tuple(ls) => ("Tuple(", ls.as_slice()),
        };
        self.push(tag)?;
        self.register_locals(ls, locals)?;
        self.push_char(')')
    }

    fn fmt_bounds(&mut self, bounds: &[Bound], locals: &mut std::collections::HashMap<LocalId, usize>, depth: usize) -> Option<()> {
        self.push_char('[')?;
        for (i, b) in bounds.iter().enumerate() {
            if i > 0 {
                self.push_char(',')?;
            }
            self.fmt_expr(&b.set, locals, depth + 1)?;
            self.push("=>")?;
            self.fmt_bound_vars(&b.vars, locals)?;
        }
        self.push_char(']')
    }

    fn fmt_expr_list(
        &mut self,
        tag: &str,
        es: &[Expr],
        locals: &mut std::collections::HashMap<LocalId, usize>,
        depth: usize,
    ) -> Option<()> {
        self.push(tag)?;
        self.push_char('(')?;
        for (i, x) in es.iter().enumerate() {
            if i > 0 {
                self.push_char(',')?;
            }
            self.fmt_expr(x, locals, depth + 1)?;
        }
        self.push_char(')')
    }

    fn fmt_field_list(
        &mut self,
        tag: &str,
        fs: &[(std::sync::Arc<str>, Expr)],
        locals: &mut std::collections::HashMap<LocalId, usize>,
        depth: usize,
    ) -> Option<()> {
        self.push(tag)?;
        self.push_char('(')?;
        for (i, (k, v)) in fs.iter().enumerate() {
            if i > 0 {
                self.push_char(',')?;
            }
            self.push(k)?;
            self.push_char(':')?;
            self.fmt_expr(v, locals, depth + 1)?;
        }
        self.push_char(')')
    }

    fn fmt_scoped_bounds_body(
        &mut self,
        prefix: &str,
        bounds: &[Bound],
        body: &Expr,
        locals: &std::collections::HashMap<LocalId, usize>,
        depth: usize,
    ) -> Option<()> {
        let mut inner = locals.clone();
        self.push(prefix)?;
        self.fmt_bounds(bounds, &mut inner, depth + 1)?;
        self.push_char(',')?;
        self.fmt_expr(body, &mut inner, depth + 1)?;
        self.push_char(')')
    }

    fn fmt_except(
        &mut self,
        base: &Expr,
        updates: &[(Vec<ExceptKey>, Expr)],
        locals: &mut std::collections::HashMap<LocalId, usize>,
        depth: usize,
    ) -> Option<()> {
        self.push("Except(")?;
        self.fmt_expr(base, locals, depth + 1)?;
        for (path, rhs) in updates {
            self.push_char(';')?;
            for k in path {
                match k {
                    ExceptKey::Field(f) => {
                        self.push_char('.')?;
                        self.push(f)?;
                    }
                    ExceptKey::Index(ixs) => {
                        self.push_char('[')?;
                        for a in ixs {
                            self.fmt_expr(a, locals, depth + 1)?;
                            self.push_char(',')?;
                        }
                        self.push_char(']')?;
                    }
                }
            }
            self.push_char('=')?;
            self.fmt_expr(rhs, locals, depth + 1)?;
        }
        self.push_char(')')
    }

    fn fmt_expr(&mut self, e: &Expr, locals: &mut std::collections::HashMap<LocalId, usize>, depth: usize) -> Option<()> {
        if self.work == 0 || depth >= MAX_CANON_DEPTH {
            return None;
        }
        self.work -= 1;
        match &*e.kind {
            ExprKind::Bool(b) => self.push(&format!("Bool({b})")),
            ExprKind::Num(n) => self.push(&format!("Num({n})")),
            ExprKind::Str(s) => self.push(&format!("Str({s:?})")),
            ExprKind::Decimal(s) => self.push(&format!("Dec({s:?})")),
            ExprKind::Var(v) => self.push(&format!("Var({})", self.program.vars[v.idx()].name)),
            ExprKind::Const(c) => self.push(&format!("Const({})", self.program.consts[c.idx()].name)),
            ExprKind::Local(l) => {
                if self.syntactic {
                    return self.push(&format!("Local({})", l.0));
                }
                match locals.get(l) {
                    Some(&id) => self.push(&format!("Local({id})")),
                    // An argument the caller expanded in its own scope: keep its
                    // identity so distinct free arguments never canonicalize alike.
                    None => self.push(&format!("Free({})", l.0)),
                }
            }
            ExprKind::At => self.push("At"),
            ExprKind::And(es) => self.fmt_expr_list("And", es, locals, depth),
            ExprKind::Or(es) => self.fmt_expr_list("Or", es, locals, depth),
            ExprKind::Tuple(es) => self.fmt_expr_list("Tuple", es, locals, depth),
            ExprKind::SetEnum(es) => self.fmt_expr_list("SetEnum", es, locals, depth),
            ExprKind::Record(fs) => self.fmt_field_list("Record", fs, locals, depth),
            ExprKind::RecordSet(fs) => self.fmt_field_list("RecordSet", fs, locals, depth),
            ExprKind::If { cond, then, els } => self.fmt_expr_list("If", &[cond.clone(), then.clone(), els.clone()], locals, depth),
            ExprKind::Case { arms, other } => {
                self.push("Case(")?;
                for (c, b) in arms {
                    self.fmt_expr(c, locals, depth + 1)?;
                    self.push("->")?;
                    self.fmt_expr(b, locals, depth + 1)?;
                    self.push_char(';')?;
                }
                if let Some(o) = other {
                    self.push("OTHER->")?;
                    self.fmt_expr(o, locals, depth + 1)?;
                }
                self.push_char(')')
            }
            ExprKind::Field { record, field } => {
                self.push("Field(")?;
                self.fmt_expr(record, locals, depth + 1)?;
                self.push(&format!(".{field})"))
            }
            ExprKind::FnApp { func, args } => {
                self.push("FnApp(")?;
                self.fmt_expr(func, locals, depth + 1)?;
                for a in args {
                    self.push_char(',')?;
                    self.fmt_expr(a, locals, depth + 1)?;
                }
                self.push_char(')')
            }
            ExprKind::FnSet { domain, range } => {
                self.push("FnSet(")?;
                self.fmt_expr(domain, locals, depth + 1)?;
                self.push("->")?;
                self.fmt_expr(range, locals, depth + 1)?;
                self.push_char(')')
            }
            ExprKind::Builtin { op, args } => {
                self.push(&format!("Builtin({op:?}"))?;
                for a in args {
                    self.push_char(',')?;
                    self.fmt_expr(a, locals, depth + 1)?;
                }
                self.push_char(')')
            }
            ExprKind::Quant { kind, bounds, body } => self.fmt_scoped_bounds_body(&format!("Quant({kind:?},"), bounds, body, locals, depth),
            ExprKind::FnConstruct { bounds, body } => self.fmt_scoped_bounds_body("FnConstruct(", bounds, body, locals, depth),
            ExprKind::SetMap { expr, bounds } => self.fmt_scoped_bounds_body("SetMap(", bounds, expr, locals, depth),
            ExprKind::SetFilter { bound, pred } => {
                self.fmt_scoped_bounds_body("SetFilter(", std::slice::from_ref(bound), pred, locals, depth)
            }
            ExprKind::Choose { vars, set, body } => {
                let mut inner = locals.clone();
                self.push("Choose(")?;
                if let Some(s) = set {
                    self.fmt_expr(s, locals, depth + 1)?;
                }
                self.push("=>")?;
                self.fmt_bound_vars(vars, &mut inner)?;
                self.push_char(',')?;
                self.fmt_expr(body, &mut inner, depth + 1)?;
                self.push_char(')')
            }
            ExprKind::Lambda { params, body } => {
                let mut inner = locals.clone();
                self.push("Lambda([")?;
                self.register_locals(params, &mut inner)?;
                self.push("],")?;
                self.fmt_expr(body, &mut inner, depth + 1)?;
                self.push_char(')')
            }
            ExprKind::Except { base, updates } => self.fmt_except(base, updates, locals, depth),
            ExprKind::BoxAction { action, sub } => self.fmt_expr_list("BoxAction", &[action.clone(), sub.clone()], locals, depth),
            ExprKind::AngleAction { action, sub } => self.fmt_expr_list("AngleAction", &[action.clone(), sub.clone()], locals, depth),
            ExprKind::Apply { op, args } if self.syntactic => {
                self.push("Apply(")?;
                self.fmt_opref(op)?;
                for a in args {
                    self.push_char(',')?;
                    self.fmt_expr(a, locals, depth + 1)?;
                }
                self.push_char(')')
            }
            ExprKind::OpArg(op) if self.syntactic => {
                self.push("OpArg(")?;
                self.fmt_opref(op)?;
                self.push_char(')')
            }
            ExprKind::InstVar { slot, subst } if self.syntactic => {
                self.push(&format!("InstVar({slot},"))?;
                self.fmt_expr(subst, locals, depth + 1)?;
                self.push_char(')')
            }
            ExprKind::Let { defs, body } if self.syntactic => {
                self.push("Let([")?;
                for (j, &d) in defs.iter().enumerate() {
                    if j > 0 {
                        self.push_char(',')?;
                    }
                    self.push(&format!("Def({}):", d.0))?;
                    let def = &self.program.defs[d.idx()];
                    match &def.kind {
                        DefKind::Op(b) => self.fmt_opt_expr(b, locals, depth + 1)?,
                        DefKind::Fn { bounds, body } => {
                            self.push("Fn(")?;
                            self.fmt_bounds(bounds, locals, depth + 1)?;
                            self.push_char(',')?;
                            self.fmt_expr(body, locals, depth + 1)?;
                            self.push_char(')')?;
                        }
                        DefKind::Pending => return None,
                    }
                }
                self.push("],")?;
                self.fmt_expr(body, locals, depth + 1)?;
                self.push_char(')')
            }
            ExprKind::QuantUnbounded { kind, vars, body } | ExprKind::TemporalQuant { kind, vars, body } if self.syntactic => {
                self.push(&format!("Unbounded({kind:?},["))?;
                for (j, l) in vars.iter().enumerate() {
                    if j > 0 {
                        self.push_char(',')?;
                    }
                    self.push(&format!("Local({})", l.0))?;
                }
                self.push("],")?;
                self.fmt_expr(body, locals, depth + 1)?;
                self.push_char(')')
            }
            ExprKind::Fairness { kind, sub, action, enabled } if self.syntactic => {
                self.push(&format!("Fairness({kind:?},"))?;
                self.fmt_expr(action, locals, depth + 1)?;
                self.push_char(',')?;
                self.fmt_expr(sub, locals, depth + 1)?;
                if let Some(e) = enabled {
                    self.push_char(',')?;
                    self.fmt_expr(e, locals, depth + 1)?;
                }
                self.push_char(')')
            }
            ExprKind::InstVar { .. }
            | ExprKind::Apply { .. }
            | ExprKind::OpArg(_)
            | ExprKind::Let { .. }
            | ExprKind::QuantUnbounded { .. }
            | ExprKind::TemporalQuant { .. }
            | ExprKind::Fairness { .. } => None,
        }
    }
}

/// Alpha-canonical, span-free, bounded representation of a normalized HIR
/// expression, used to connect declared `.cfg` constant substitutions to the
/// exact normalized expansion spliced into an emitted certificate.
pub(in crate::optimize::phase) fn canonical_expr_repr(program: &Program, e: &Expr) -> Option<String> {
    canonical_expr_repr_with_limits(program, e, MAX_CANON_WORK, MAX_CANON_BYTES)
}

fn canonical_expr_repr_with_limits(program: &Program, e: &Expr, work: usize, max_bytes: usize) -> Option<String> {
    expr_repr_with_limits(program, e, work, max_bytes, false)
}

fn expr_repr_with_limits(program: &Program, e: &Expr, work: usize, max_bytes: usize, syntactic: bool) -> Option<String> {
    let mut w = CanonWriter { program, next_id: 0, work, max_bytes, out: String::new(), syntactic };
    w.fmt_expr(e, &mut std::collections::HashMap::new(), 0)?;
    Some(w.out)
}

/// Span-free syntactic representation of a normalized HIR expression: local ids
/// are printed verbatim, so the text of a subexpression recorded at an override
/// use site occurs verbatim inside the normalized model formula that contains it.
pub(in crate::optimize::phase) fn syntactic_expr_repr(program: &Program, e: &Expr) -> Option<String> {
    expr_repr_with_limits(program, e, MAX_CANON_WORK, MAX_CANON_BYTES, true)
}

fn write_const_subst_tree(body: &mut String, vals: &[&str], lo: usize, hi: usize, indent: usize) {
    use std::fmt::Write;
    let pad = " ".repeat(indent);
    if hi - lo == 1 {
        writeln!(body, "{pad}if i.val = {lo} then {} else \"\"", crate::optimize::lean::literal(vals[lo])).unwrap();
        return;
    }
    let mid = lo + (hi - lo) / 2;
    writeln!(body, "{pad}if i.val < {mid} then").unwrap();
    write_const_subst_tree(body, vals, lo, mid, indent + 2);
    writeln!(body, "{pad}else").unwrap();
    write_const_subst_tree(body, vals, mid, hi, indent + 2);
}

fn write_const_subst_fn(body: &mut String, count: &str, fn_name: &str, vals: &[&str]) {
    use std::fmt::Write;
    writeln!(body, "def {fn_name} (i : Fin {count}) : String :=").unwrap();
    write_const_subst_tree(body, vals, 0, vals.len(), 2);
}

/// When zero-arity `CONSTANT C <- target` substitutions were actually expanded
/// by the normalizer into the emitted model, independently compute each declared
/// binding's canonical HIR from `cfg` + `program`, verify it matches the
/// normalizer's recorded expansion (failing closed `None` on any mismatch or
/// unsupported binding count), append the Lean binding-agreement and
/// premise-free certificate-lifting theorems, and close `TlxOptimization.<namespace>` once.
pub(in crate::optimize::phase) fn attach_const_subst_obligation(
    program: &Program,
    cfg: &Config,
    expanded_substs: &std::collections::BTreeMap<ConstId, String>,
    overrides: &OverrideObligations<'_>,
    declare: impl Fn(ConstId) -> Option<String>,
    declare_override: impl Fn(&str, &[Expr]) -> Option<String>,
    cert: OpenCert,
) -> Option<String> {
    use std::fmt::Write;
    let OpenCert { mut body, namespace, constrained } = cert;
    if expanded_substs.len() > MAX_CERT_CONST_SUBSTS || overrides.applied.len() > MAX_CERT_CONST_SUBSTS {
        return None;
    }
    let model_hirs = overrides.model_hirs;
    if !overrides.applied.is_empty() {
        struct Row {
            name: String,
            target: String,
            declared: String,
            applied_canonical: String,
            applied: String,
            model: String,
            prefix: String,
            suffix: String,
        }
        // The expansion the lowering spliced must be the configured declaration
        // (`def_subst_bindings_match`), and it must occur at its own use site in
        // a normalized model formula. `defSubstModelHIR` is that formula; the
        // guarded systems below consume `overrideGuard`, so a changed table
        // changes the concrete system or breaks its proof.
        let mut rows: Vec<Row> = Vec::new();
        let mut seen: std::collections::BTreeSet<(String, Vec<String>)> = std::collections::BTreeSet::new();
        let mut occurrences: std::collections::HashMap<(usize, String), usize> = std::collections::HashMap::new();
        for o in overrides.applied {
            let declared = declare_override(&o.name, &o.args)?;
            if declared != o.applied || o.applied_syntax.is_empty() {
                return None;
            }
            let key = (o.name.clone(), o.args.iter().map(|a| canonical_expr_repr(program, a)).collect::<Option<Vec<_>>>()?);
            if !seen.insert(key) {
                continue;
            }
            let (model, prefix, suffix) = model_hirs.iter().enumerate().find_map(|(mi, m)| {
                let seen = occurrences.entry((mi, o.applied_syntax.clone())).or_insert(0);
                let at = m.match_indices(o.applied_syntax.as_str()).nth(*seen).map(|(at, _)| at)?;
                *seen += 1;
                Some((m.clone(), m[..at].to_string(), m[at + o.applied_syntax.len()..].to_string()))
            })?;
            rows.push(Row {
                name: o.name.clone(),
                target: o.target.clone(),
                declared,
                applied_canonical: o.applied.clone(),
                applied: o.applied_syntax.clone(),
                model,
                prefix,
                suffix,
            });
        }
        rows.sort_by(|a, b| a.name.cmp(&b.name).then_with(|| a.applied.cmp(&b.applied)));
        // A composed constrained certificate keeps separate stage systems; the
        // guard would need one equality per stage. Refuse overrides there rather
        // than emit an unguarded constrained certificate.
        if constrained && body.contains("def constrainedIntermediate := ") {
            return None;
        }
        let mut header = String::new();
        header.push_str("set_option maxRecDepth 100000\n");
        writeln!(header, "abbrev DefSubstCount : Nat := {}", rows.len()).unwrap();
        write_const_subst_fn(&mut header, "DefSubstCount", "defSubstName", &rows.iter().map(|r| r.name.as_str()).collect::<Vec<_>>());
        write_const_subst_fn(&mut header, "DefSubstCount", "defSubstTarget", &rows.iter().map(|r| r.target.as_str()).collect::<Vec<_>>());
        write_const_subst_fn(
            &mut header,
            "DefSubstCount",
            "defSubstDeclared",
            &rows.iter().map(|r| r.declared.as_str()).collect::<Vec<_>>(),
        );
        write_const_subst_fn(
            &mut header,
            "DefSubstCount",
            "defSubstAppliedCanonical",
            &rows.iter().map(|r| r.applied_canonical.as_str()).collect::<Vec<_>>(),
        );
        write_const_subst_fn(&mut header, "DefSubstCount", "defSubstApplied", &rows.iter().map(|r| r.applied.as_str()).collect::<Vec<_>>());
        write_const_subst_fn(&mut header, "DefSubstCount", "defSubstModelHIR", &rows.iter().map(|r| r.model.as_str()).collect::<Vec<_>>());
        write_const_subst_fn(
            &mut header,
            "DefSubstCount",
            "defSubstModelPrefix",
            &rows.iter().map(|r| r.prefix.as_str()).collect::<Vec<_>>(),
        );
        write_const_subst_fn(
            &mut header,
            "DefSubstCount",
            "defSubstModelSuffix",
            &rows.iter().map(|r| r.suffix.as_str()).collect::<Vec<_>>(),
        );
        header.push_str(
            "theorem def_subst_bindings_match :\n\
             \x20 ∀ i : Fin DefSubstCount, defSubstDeclared i = defSubstAppliedCanonical i := by\n\
             \x20 intro i; rfl\n\
             def overrideEmpty (S : Type) : System S :=\n\
             \x20 { initial := fun _ => False, next := fun _ _ => False, safe := fun _ => True }\n\
             def overrideEmptyConstrained (S : Type) : ConstrainedSystem S :=\n\
             \x20 { toSystem := overrideEmpty S, initSafe := fun _ => True, constraint := fun _ => True,\n\
             \x20   actionConstraint := fun _ _ => True, actionSafe := fun _ _ => True }\n\
             def overrideGuard : Prop :=\n",
        );
        for (i, _) in rows.iter().enumerate() {
            let ix = format!("⟨{i}, by decide⟩");
            writeln!(
                header,
                "  (defSubstDeclared {ix} = defSubstAppliedCanonical {ix}) ∧\n  (defSubstModelHIR {ix} = defSubstModelPrefix {ix} ++ defSubstApplied {ix} ++ defSubstModelSuffix {ix}){}",
                if i + 1 < rows.len() { " ∧" } else { "" }
            )
            .unwrap();
        }
        for (i, _) in rows.iter().enumerate() {
            let ix = format!("⟨{i}, by decide⟩");
            writeln!(header, "set_option maxRecDepth 100000 in").unwrap();
            writeln!(header, "theorem def_subst_model_slice_{i} :").unwrap();
            writeln!(
                header,
                "  defSubstModelHIR {ix} = defSubstModelPrefix {ix} ++ defSubstApplied {ix} ++ defSubstModelSuffix {ix} := by"
            )
            .unwrap();
            writeln!(header, "  rfl").unwrap();
            writeln!(header, "#print axioms def_subst_model_slice_{i}").unwrap();
        }
        header.push_str("instance overrideGuardDecidable : Decidable overrideGuard := by\n  unfold overrideGuard\n  infer_instance\n");
        header.push_str("set_option maxRecDepth 100000 in\ntheorem override_consistent : overrideGuard :=\n  ⟨");
        for i in 0..rows.len() * 2 {
            if i > 0 {
                header.push_str(", ");
            }
            header.push_str("by rfl");
        }
        header.push_str("⟩\n#print axioms def_subst_bindings_match\n");
        // Guard the ordinary concrete system, then rewrite its certificate.
        let pos = body.find("def before := ")?;
        body.insert_str(pos, &header);
        let pos = body.find("def before := ")?;
        let line_end = pos + body[pos..].find('\n')?;
        let rhs = body[pos + "def before := ".len()..line_end].trim().to_string();
        body.replace_range(
            pos..line_end,
            &format!("set_option maxRecDepth 100000 in\ndef before := if overrideGuard then {rhs} else overrideEmpty _"),
        );
        let before_key = "theorem certificate : Certificate (before sem) (after sem) (project sem) :=";
        let header_at = body.find(before_key)?;
        body.insert_str(header_at, "set_option maxRecDepth 100000 in\n");
        let pos = body.find(before_key)? + before_key.len();
        let next = body[pos..].find("\ntheorem ")? + pos;
        let proof = body[pos..next].trim().to_string();
        body.replace_range(
            pos..next,
            &format!(" by\n  have h : overrideGuard := override_consistent\n  unfold before\n  rw [ite_eq_left h]\n  exact {proof}\n"),
        );
        if constrained {
            let key = "def constrainedBefore := ";
            let pos = body.find(key)?;
            let line_end = pos + body[pos..].find('\n')?;
            let rhs = body[pos + key.len()..line_end].trim().to_string();
            body.replace_range(
                pos..line_end,
                &format!("set_option maxRecDepth 100000 in\ndef constrainedBefore := if overrideGuard then {rhs} else overrideEmptyConstrained _"),
            );
            let before_key = "theorem constrained_certificate :\n  ConstrainedCertificate (constrainedBefore sem) (constrainedAfter sem) (project sem) :=";
            let header_at = body.find(before_key)?;
            body.insert_str(header_at, "set_option maxRecDepth 100000 in\n");
            let pos = body.find(before_key)? + before_key.len();
            let next = body[pos..].find("\ntheorem ")? + pos;
            let proof = body[pos..next].trim().to_string();
            body.replace_range(
                pos..next,
                &format!(" by\n  have h : overrideGuard := override_consistent\n  unfold constrainedBefore\n  rw [ite_eq_left h]\n  exact {proof}\n"),
            );
        }
        body.push_str("set_option maxRecDepth 100000 in\ntheorem certificate_with_overrides :\n  Certificate (before sem) (after sem) (project sem) ∧\n");
        if constrained {
            body.push_str("  ConstrainedCertificate (constrainedBefore sem) (constrainedAfter sem) (project sem) ∧\n");
        }
        body.push_str("  overrideGuard :=\n  ⟨certificate sem");
        if constrained {
            body.push_str(", constrained_certificate sem");
        }
        body.push_str(", override_consistent⟩\n#print axioms certificate_with_overrides\n");
    }
    if !expanded_substs.is_empty() {
        let mut entries: Vec<(String, String, String, String)> = Vec::with_capacity(expanded_substs.len());
        for (&cid, expanded_hir) in expanded_substs {
            let name = program.consts[cid.idx()].name.to_string();
            let target = cfg.last_constant_subst(&name)?.to_string();
            let declared_hir = declare(cid)?;
            if &declared_hir != expanded_hir {
                return None;
            }
            entries.push((name, target, declared_hir, expanded_hir.clone()));
        }
        entries.sort_by(|a, b| a.0.cmp(&b.0));

        writeln!(body, "abbrev ConstSubstCount : Nat := {}", entries.len()).unwrap();
        let names: Vec<&str> = entries.iter().map(|e| e.0.as_str()).collect();
        let targets: Vec<&str> = entries.iter().map(|e| e.1.as_str()).collect();
        let declared: Vec<&str> = entries.iter().map(|e| e.2.as_str()).collect();
        let expanded: Vec<&str> = entries.iter().map(|e| e.3.as_str()).collect();
        write_const_subst_fn(&mut body, "ConstSubstCount", "constSubstConst", &names);
        write_const_subst_fn(&mut body, "ConstSubstCount", "constSubstTarget", &targets);
        write_const_subst_fn(&mut body, "ConstSubstCount", "constSubstDeclared", &declared);
        write_const_subst_fn(&mut body, "ConstSubstCount", "constSubstExpanded", &expanded);
        body.push_str(
            "theorem const_subst_bindings_match :\n\
             \x20 ∀ i : Fin ConstSubstCount, constSubstDeclared i = constSubstExpanded i := by\n\
             \x20 intro i; rfl\n",
        );
        body.push_str(
            "theorem const_subst_sound {ConstVal : Type}\n\
             \x20 (eval : String → ConstVal)\n\
             \x20 (sys : (Fin ConstSubstCount → ConstVal) → System _)\n\
             \x20 (hModel : sys (fun i => eval (constSubstExpanded i)) = before sem) :\n\
             \x20 Certificate (sys (fun i => eval (constSubstDeclared i))) (after sem) (project sem) :=\n\
             \x20 const_subst_certificate sys (after sem) (project sem)\n\
             \x20   (fun i => eval (constSubstDeclared i))\n\
             \x20   (fun i => eval (constSubstExpanded i))\n\
             \x20   (fun i => congrArg eval (const_subst_bindings_match i))\n\
             \x20   (hModel ▸ certificate sem)\n\
             #print axioms const_subst_bindings_match\n\
             #print axioms const_subst_sound\n",
        );
        if constrained {
            body.push_str(
                "theorem const_subst_constrained_sound {ConstVal : Type}\n\
                 \x20 (eval : String → ConstVal)\n\
                 \x20 (sys : (Fin ConstSubstCount → ConstVal) → ConstrainedSystem _)\n\
                 \x20 (hModel : sys (fun i => eval (constSubstExpanded i)) = constrainedBefore sem) :\n\
                 \x20 ConstrainedCertificate (sys (fun i => eval (constSubstDeclared i))) (constrainedAfter sem) (project sem) :=\n\
                 \x20 const_subst_constrained_certificate sys (constrainedAfter sem) (project sem)\n\
                 \x20   (fun i => eval (constSubstDeclared i))\n\
                 \x20   (fun i => eval (constSubstExpanded i))\n\
                 \x20   (fun i => congrArg eval (const_subst_bindings_match i))\n\
                 \x20   (hModel ▸ constrained_certificate sem)\n\
                 #print axioms const_subst_constrained_sound\n",
            );
        }
    }
    writeln!(body, "end\nend TlxOptimization.{namespace}").unwrap();
    Some(body)
}

#[cfg(test)]
mod const_subst_tests {
    use super::*;
    use crate::hir::{DefKind, OpRef};
    use crate::optimize::phase::{normalize, SymNormalizer};
    use std::collections::BTreeMap;
    use tlx_front::cfg::parse_cfg;

    #[test]
    fn attach_const_subst_obligation_rejects_mismatched_expansion_for_fixed_declaration() {
        let tla = "---- MODULE SubstMismatch ----\nCONSTANT C\nVARIABLE x\nOne == 1\nTwo == 2\nInit == x = C\nNext == x' = x\n====\n";
        let cfg_src = "INIT Init\nNEXT Next\nCONSTANT C <- Two\n";
        let dir = tlx_testkit::TempDir::with_spec("subst-mismatch", tla, cfg_src);
        let program = Program::load(&dir.join("SubstMismatch.tla"), &[]).unwrap();
        let cfg = parse_cfg(cfg_src).unwrap();
        let cid = ConstId(0);
        let dummy_cert = OpenCert::new("namespace TlxOptimization.GeneratedTest\n".to_owned(), "", "GeneratedTest", false, false, false);

        // Matching expansion (`Num(2)` for `C <- Two`) succeeds and records canonical lowered HIR.
        let good = BTreeMap::from([(cid, "Num(2)".to_owned())]);
        let emitted = attach_const_subst_obligation(
            &program,
            &cfg,
            &good,
            &OverrideObligations { applied: &[], model_hirs: &[] },
            |c| normalize::Normalizer::expand_declared_const_subst(&program, &cfg, c),
            |_, _| None,
            dummy_cert.clone(),
        )
        .expect("matching expansion should emit obligation");
        assert!(emitted.contains("def constSubstDeclared"));
        assert!(emitted.contains("def constSubstExpanded"));
        assert!(emitted.contains("\"Num(2)\""));
        assert!(!emitted.contains("const_subst_constrained_sound"));
        assert!(emitted.ends_with("end\nend TlxOptimization.GeneratedTest\n"));

        // Constrained flag explicitly selects `const_subst_constrained_sound`.
        let constrained_cert =
            OpenCert::new("namespace TlxOptimization.GeneratedTest\n".to_owned(), "", "GeneratedTest", true, false, false);
        let constrained_emitted = attach_const_subst_obligation(
            &program,
            &cfg,
            &good,
            &OverrideObligations { applied: &[], model_hirs: &[] },
            |c| normalize::Normalizer::expand_declared_const_subst(&program, &cfg, c),
            |_, _| None,
            constrained_cert,
        )
        .expect("constrained expansion should emit constrained obligation");
        assert!(constrained_emitted.contains("theorem const_subst_constrained_sound"));
        assert!(constrained_emitted.ends_with("end\nend TlxOptimization.GeneratedTest\n"));

        // Mismatched expansion (`Num(1)` while declaration stays `C <- Two`) MUST be refused.
        let bad = BTreeMap::from([(cid, "Num(1)".to_owned())]);
        assert!(attach_const_subst_obligation(
            &program,
            &cfg,
            &bad,
            &OverrideObligations { applied: &[], model_hirs: &[] },
            |c| normalize::Normalizer::expand_declared_const_subst(&program, &cfg, c),
            |_, _| None,
            dummy_cert,
        )
        .is_none());
    }

    #[test]
    fn canonical_expr_repr_distinguishes_many_and_tuple_binders_and_builtin_nat() {
        let tla = r#"---- MODULE BinderSubst ----
EXTENDS Naturals
CONSTANT C, D
VARIABLE x
S == {<<1, 2>>}
TruthMany == \E a, b \in S : a = b
TruthTuple == \E <<a, b>> \in S : a = b
ChooseMany == CHOOSE a \in S : TRUE
ChooseTuple == CHOOSE <<a, b>> \in S : a < b
Init == x = 0
Next == x' = x
====
"#;
        let cfg_many = "INIT Init\nNEXT Next\nCONSTANTS\n  C <- TruthMany\n  D <- Nat\n";
        let cfg_tuple = "INIT Init\nNEXT Next\nCONSTANTS\n  C <- TruthTuple\n  D <- Nat\n";
        let dir = tlx_testkit::TempDir::with_spec("binder-subst", tla, cfg_many);
        let program = Program::load(&dir.join("BinderSubst.tla"), &[]).unwrap();
        let cm = parse_cfg(cfg_many).unwrap();
        let ct = parse_cfg(cfg_tuple).unwrap();
        let cid = ConstId(0);
        let did = ConstId(1);

        let repr_many = normalize::Normalizer::expand_declared_const_subst(&program, &cm, cid).unwrap();
        let repr_tuple = normalize::Normalizer::expand_declared_const_subst(&program, &ct, cid).unwrap();
        assert_ne!(repr_many, repr_tuple, "Many vs Tuple binders must not conflate: {repr_many}");
        assert!(repr_many.contains("Many("), "{repr_many}");
        assert!(repr_tuple.contains("Tuple("), "{repr_tuple}");

        // CHOOSE binder variants must also remain distinct.
        let mut n = normalize::Normalizer::with_config(&program, &cm);
        let def = |name: &str| {
            let d = program.defs.iter().find(|d| &*d.name == name).unwrap();
            let DefKind::Op(e) = &d.kind else { panic!() };
            e.clone()
        };
        let cm_repr = canonical_expr_repr(&program, &n.root(&def("ChooseMany")).unwrap()).unwrap();
        let ct_repr = canonical_expr_repr(&program, &n.root(&def("ChooseTuple")).unwrap()).unwrap();
        assert_ne!(cm_repr, ct_repr);
        assert!(cm_repr.contains("Choose(") && cm_repr.contains("Many("), "{cm_repr}");
        assert!(ct_repr.contains("Choose(") && ct_repr.contains("Tuple("), "{ct_repr}");

        // Swapping Many/Tuple expansions against a fixed declaration MUST be refused.
        let dummy_cert = OpenCert::new("namespace TlxOptimization.GeneratedTest\n".to_owned(), "", "GeneratedTest", false, false, false);
        assert!(attach_const_subst_obligation(
            &program,
            &cm,
            &BTreeMap::from([(cid, repr_tuple.clone())]),
            &OverrideObligations { applied: &[], model_hirs: &[] },
            |c| normalize::Normalizer::expand_declared_const_subst(&program, &cm, c),
            |_, _| None,
            dummy_cert.clone(),
        )
        .is_none());
        assert!(attach_const_subst_obligation(
            &program,
            &ct,
            &BTreeMap::from([(cid, repr_many.clone())]),
            &OverrideObligations { applied: &[], model_hirs: &[] },
            |c| normalize::Normalizer::expand_declared_const_subst(&program, &ct, c),
            |_, _| None,
            dummy_cert.clone(),
        )
        .is_none());

        // Builtin `D <- Nat` MUST resolve to `Builtin(Nat)`, never the placeholder `SetEnum()`.
        let nat_repr = normalize::Normalizer::expand_declared_const_subst(&program, &cm, did).unwrap();
        assert_eq!(nat_repr, "Builtin(Nat)");
        assert!(attach_const_subst_obligation(
            &program,
            &cm,
            &BTreeMap::from([(did, "SetEnum()".to_owned())]),
            &OverrideObligations { applied: &[], model_hirs: &[] },
            |c| normalize::Normalizer::expand_declared_const_subst(&program, &cm, c),
            |_, _| None,
            dummy_cert,
        )
        .is_none());
    }

    #[test]
    fn canonical_expr_repr_alpha_renames_lambdas_rejects_raw_forms_and_bounds_work() {
        let tla = r#"---- MODULE LambdaSubst ----
EXTENDS Naturals, Sequences
CONSTANT C
VARIABLE x
Pos(v) == v > 0
Filtered == SelectSeq(<<1, 2>>, Pos)
Init == x = 0
Next == x' = x
====
"#;
        let cfg_src = "INIT Init\nNEXT Next\nCONSTANT C <- Filtered\n";
        let dir = tlx_testkit::TempDir::with_spec("lambda-subst", tla, cfg_src);
        let program = Program::load(&dir.join("LambdaSubst.tla"), &[]).unwrap();
        let cfg = parse_cfg(cfg_src).unwrap();

        // Equivalent `Lambda` nodes with distinct `LocalId`s and non-default `Span`s
        // must produce identical canonical bytes without leaking raw IDs or spans.
        let s1 = program.defs[0].span;
        let s2 = program.defs.last().unwrap().span;
        assert_ne!(s1, s2);
        let lam1 = Expr::new(
            ExprKind::Lambda {
                params: vec![LocalId(7)],
                body: Expr::new(
                    ExprKind::Builtin {
                        op: B::Gt,
                        args: vec![Expr::new(ExprKind::Local(LocalId(7)), s1), Expr::new(ExprKind::Num(0), s1)],
                    },
                    s1,
                ),
            },
            s1,
        );
        let lam2 = Expr::new(
            ExprKind::Lambda {
                params: vec![LocalId(999)],
                body: Expr::new(
                    ExprKind::Builtin {
                        op: B::Gt,
                        args: vec![Expr::new(ExprKind::Local(LocalId(999)), s2), Expr::new(ExprKind::Num(0), s2)],
                    },
                    s2,
                ),
            },
            s2,
        );
        let r1 = canonical_expr_repr(&program, &lam1).unwrap();
        let r2 = canonical_expr_repr(&program, &lam2).unwrap();
        assert_eq!(r1, "Lambda([L0],Builtin(Gt,Local(0),Num(0)))");
        assert_eq!(r1, r2);

        // `SelectSeq` in `SymNormalizer::for_equiv_with_config` builds fresh unary `Lambda`
        // locals on each expansion; recorded and declared representations must match.
        let mut sym = SymNormalizer::for_equiv_with_config(&program, &cfg);
        let c_expr = Expr::new(ExprKind::Const(ConstId(0)), Span::default());
        assert!(sym.normalize(&c_expr).is_some());
        let cert = OpenCert::new("namespace TlxOptimization.GeneratedTest\n".to_owned(), "", "GeneratedTest", false, false, false);
        let attached = sym.attach_const_subst(cert).expect("SelectSeq lambda substitution should match declared expansion");
        assert!(attached.contains("Lambda([L0],Builtin(Gt,Local(0),Num(0)))"), "{attached}");

        // A caller-expanded argument keeps its identity, so two distinct free
        // arguments never canonicalize alike; un-normalized raw HIR still fails.
        let free = canonical_expr_repr(&program, &Expr::new(ExprKind::Local(LocalId(42)), s1)).unwrap();
        assert_eq!(free, "Free(42)");
        assert_ne!(free, canonical_expr_repr(&program, &Expr::new(ExprKind::Local(LocalId(7)), s1)).unwrap());
        assert!(canonical_expr_repr(&program, &Expr::new(ExprKind::OpArg(OpRef::Builtin(B::Plus)), s1)).is_none());

        // Shared `Arc` tree (`2^18` occurrences via `Tuple([t, t])`) must hit work/byte limits cleanly.
        let mut dag = Expr::new(ExprKind::Num(1), Span::default());
        for _ in 0..18 {
            dag = Expr::new(ExprKind::Tuple(vec![dag.clone(), dag]), Span::default());
        }
        assert!(canonical_expr_repr(&program, &dag).is_none());
        assert!(canonical_expr_repr_with_limits(&program, &lam1, 2, 1024).is_none());
        assert!(canonical_expr_repr_with_limits(&program, &lam1, 100, 10).is_none());
    }

    #[test]
    fn attach_const_subst_obligation_scales_to_cap_and_refuses_above_limit() {
        let count = MAX_CERT_CONST_SUBSTS + 1;
        let mut tla = String::from("---- MODULE ManyConsts ----\nCONSTANT ");
        tla.push_str(&(0..count).map(|i| format!("C{i}")).collect::<Vec<_>>().join(", "));
        tla.push_str("\nVARIABLE x\nOne == 1\nInit == x = 0\nNext == x' = x\n====\n");
        let mut cfg_src = String::from("INIT Init\nNEXT Next\nCONSTANTS\n");
        for i in 0..count {
            cfg_src.push_str(&format!("  C{i} <- One\n"));
        }
        let dir = tlx_testkit::TempDir::with_spec("many-consts", &tla, &cfg_src);
        let program = Program::load(&dir.join("ManyConsts.tla"), &[]).unwrap();
        let cfg = parse_cfg(&cfg_src).unwrap();
        let cert = OpenCert::new("namespace TlxOptimization.GeneratedTest\n".to_owned(), "", "GeneratedTest", false, false, false);

        let at_cap: BTreeMap<ConstId, String> = (0..MAX_CERT_CONST_SUBSTS).map(|i| (ConstId(i as u32), "Num(1)".into())).collect();
        let ok = attach_const_subst_obligation(
            &program,
            &cfg,
            &at_cap,
            &OverrideObligations { applied: &[], model_hirs: &[] },
            |c| normalize::Normalizer::expand_declared_const_subst(&program, &cfg, c),
            |_, _| None,
            cert.clone(),
        )
        .expect("MAX_CERT_CONST_SUBSTS bindings should emit balanced tree obligation");
        assert!(ok.contains("intro i; rfl"));

        let over_cap: BTreeMap<ConstId, String> = (0..count).map(|i| (ConstId(i as u32), "Num(1)".into())).collect();
        assert!(attach_const_subst_obligation(
            &program,
            &cfg,
            &over_cap,
            &OverrideObligations { applied: &[], model_hirs: &[] },
            |c| normalize::Normalizer::expand_declared_const_subst(&program, &cfg, c),
            |_, _| None,
            cert,
        )
        .is_none());
    }
}
