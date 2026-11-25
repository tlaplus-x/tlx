//! Structural state projections: field liveness, sequence length and finite
//! history summaries. These reuse normalized branches and forward domains.

mod age;
mod choose_sym;
mod domain;
mod equiv_sym;
mod erasure;
mod history;
mod keyed;
mod liveness;
mod normalize;
mod ordered;
mod sequence;
mod sym_groups;
pub(crate) mod sym_norm;
mod sym_totality;

pub use age::{age_projection, age_projection_with_spec};
pub use choose_sym::{choose_symmetry_certificate, choose_symmetry_certificate_with_spec};
pub use equiv_sym::{
    symmetry_certificate as equiv_symmetry_certificate, symmetry_certificate_with_spec as equiv_symmetry_certificate_with_spec,
};
pub use erasure::{unobserved_projection, unobserved_projection_with_spec};
pub use history::{history_projection, history_projection_with_spec};
pub use ordered::{ordered_projection, ordered_projection_with_spec, OrderedHistory, OrderedPlan, OrderedShape};
pub use sequence::{sequence_length_projection, sequence_length_projection_with_spec};
pub use sym_norm::{infer_var_domains, proves_var_membership, SymNormalizer};
pub use sym_totality::cfg_constants_supported;

/// All safety-level observations and admission constraints checked by `tlx-runtime`.
#[derive(Clone, Copy, Debug, Default)]
pub struct CheckSpec<'a> {
    /// State invariants (`INVARIANT` and `[]P` properties), checked on every Init and Next state.
    pub invariants: &'a [Expr],
    /// State-level `PROPERTY` conjuncts (`init_props`), checked on every Init state.
    pub init_props: &'a [Expr],
    /// State `CONSTRAINT` predicates governing admission into `AdmittedReachable`.
    pub constraints: &'a [Expr],
    /// Action `ACTION_CONSTRAINT` predicates governing transition admission into `AdmittedReachable`.
    pub action_constraints: &'a [Expr],
    /// Action `PROPERTY` conjuncts (`[][A]_sub`), checked on every Next transition from `AdmittedReachable`.
    pub action_props: &'a [Expr],
}

impl<'a> CheckSpec<'a> {
    pub fn invariants_only(invariants: &'a [Expr]) -> Self {
        Self { invariants, ..Self::default() }
    }

    pub fn is_constrained(&self) -> bool {
        !self.init_props.is_empty() || !self.constraints.is_empty() || !self.action_constraints.is_empty() || !self.action_props.is_empty()
    }

    pub fn has_action_checks(&self) -> bool {
        !self.action_constraints.is_empty() || !self.action_props.is_empty()
    }

    pub fn all_state_preds(&self) -> impl Iterator<Item = &'a Expr> {
        self.invariants.iter().chain(self.init_props.iter()).chain(self.constraints.iter())
    }

    pub fn all_exprs(&self) -> impl Iterator<Item = &'a Expr> {
        self.invariants
            .iter()
            .chain(self.init_props.iter())
            .chain(self.constraints.iter())
            .chain(self.action_constraints.iter())
            .chain(self.action_props.iter())
    }

    pub(in crate::optimize::phase) fn state_only(self) -> Option<Self> {
        (!self.has_action_checks()).then_some(self)
    }

    pub(in crate::optimize::phase) fn try_map(self, mut f: impl FnMut(&Expr) -> Option<Expr>) -> Option<OwnedCheckSpec> {
        Some(OwnedCheckSpec {
            invariants: self.invariants.iter().map(&mut f).collect::<Option<_>>()?,
            init_props: self.init_props.iter().map(&mut f).collect::<Option<_>>()?,
            constraints: self.constraints.iter().map(&mut f).collect::<Option<_>>()?,
            action_constraints: self.action_constraints.iter().map(&mut f).collect::<Option<_>>()?,
            action_props: self.action_props.iter().map(&mut f).collect::<Option<_>>()?,
        })
    }
}

/// Lowered observation and constraint strings passed by name into symmetry emitters.
pub(in crate::optimize::phase) struct ObsBundle<'a> {
    pub observation: &'a str,
    pub init_observation: &'a str,
    pub constraint_test: &'a str,
    pub action_constraint_test: &'a str,
    pub action_observation: &'a str,
    pub constrained: bool,
}

/// Owned counterpart of [`CheckSpec`] for normalized predicate vectors.
#[derive(Clone, Debug, Default)]
pub(in crate::optimize::phase) struct OwnedCheckSpec {
    pub invariants: Vec<Expr>,
    pub init_props: Vec<Expr>,
    pub constraints: Vec<Expr>,
    pub action_constraints: Vec<Expr>,
    pub action_props: Vec<Expr>,
}

impl OwnedCheckSpec {
    pub(in crate::optimize::phase) fn as_spec(&self) -> CheckSpec<'_> {
        CheckSpec {
            invariants: &self.invariants,
            init_props: &self.init_props,
            constraints: &self.constraints,
            action_constraints: &self.action_constraints,
            action_props: &self.action_props,
        }
    }
}

/// Resolved target of a zero-arity `CONSTANT C <- target` `.cfg` substitution.
#[derive(Clone, Copy, Debug)]
pub(in crate::optimize::phase) enum ConstSubstTarget {
    PureBuiltin(B, Span),
    Def(DefId),
    Const(ConstId),
}

/// Resolve a `.cfg` substitution RHS symbol name into a pure zero-arity builtin,
/// non-`LET` zero-arity root definition, or zero-arity constant.
pub(in crate::optimize::phase) fn resolve_const_subst_name(program: &Program, target: &str) -> Option<ConstSubstTarget> {
    match program.lookup_resolved_root(target)? {
        RootSymbol::Def(did) => {
            let d = &program.defs[did.idx()];
            if !d.params.is_empty() || program.def_is_let(did) {
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

/// An emitted Lean certificate body whose `TlxOptimization.<namespace>` section
/// remains open until optional constrained and constant-substitution obligations
/// are appended and the namespace is closed once.
#[derive(Clone)]
pub(in crate::optimize::phase) struct OpenCert {
    body: String,
    namespace: &'static str,
    constrained: bool,
}

impl OpenCert {
    pub(in crate::optimize::phase) fn new(
        mut body: String,
        tail: &str,
        namespace: &'static str,
        constrained: bool,
        include_erasure_cert: bool,
        is_choose: bool,
    ) -> Self {
        body.push_str(tail);
        if !body.is_empty() && !body.ends_with('\n') {
            body.push('\n');
        }
        if constrained {
            push_constrained_theorems(&mut body, include_erasure_cert, is_choose);
        }
        Self { body, namespace, constrained }
    }
}

fn push_constrained_theorems(out: &mut String, include_erasure_cert: bool, is_choose: bool) {
    if is_choose {
        out.push_str(
            "def rawConstrainedBefore := (model sem).rawConstrained\n\
             def constrainedBefore := (model sem).validConstrained\n\
             def constrainedAfter := (model sem).constrainedReduced\n\
             theorem constrained_certificate :\n\
             \x20 ConstrainedCertificate (constrainedBefore sem) (constrainedAfter sem) (project sem) :=\n\
             \x20 (model sem).constrained_certificate\n\
             theorem constrained_optimization_correct :\n\
             \x20 ConstrainedSafe (rawConstrainedBefore sem) ↔ ConstrainedSafe (constrainedAfter sem) :=\n\
             \x20 (model sem).constrained_optimization_correct\n\
             theorem constrained_init_counterexample_lifts {a}\n\
             \x20 (ha : (constrainedAfter sem).initial a)\n\
             \x20 (bad : ¬ ((constrainedAfter sem).safe a ∧ (constrainedAfter sem).initSafe a)) :\n\
             \x20 ∃ s : (model sem).ValidState, (rawConstrainedBefore sem).initial s.val ∧ project sem s = a ∧\n\
             \x20   ¬ ((rawConstrainedBefore sem).safe s.val ∧ (rawConstrainedBefore sem).initSafe s.val) :=\n\
             \x20 (model sem).constrained_init_counterexample_lifts ha bad\n\
             theorem constrained_step_counterexample_lifts {a b}\n\
             \x20 (ha : AdmittedReachable (constrainedAfter sem) a)\n\
             \x20 (hab : (constrainedAfter sem).next a b)\n\
             \x20 (bad : ¬ ((constrainedAfter sem).safe b ∧ (constrainedAfter sem).actionSafe a b)) :\n\
             \x20 ∃ s t : (model sem).ValidState, AdmittedReachable (rawConstrainedBefore sem) s.val ∧ (rawConstrainedBefore sem).next s.val t.val ∧\n\
             \x20   project sem s = a ∧ project sem t = b ∧\n\
             \x20   ¬ ((rawConstrainedBefore sem).safe t.val ∧ (rawConstrainedBefore sem).actionSafe s.val t.val) :=\n\
             \x20 (model sem).constrained_step_counterexample_lifts ha hab bad\n\
             theorem admitted_deadlock_preserved :\n\
             \x20 (∃ s : (model sem).RState, AdmittedReachable (rawConstrainedBefore sem) s ∧ ¬ ∃ t : (model sem).RState, (rawConstrainedBefore sem).next s t) ↔\n\
             \x20 (∃ a, AdmittedReachable (constrainedAfter sem) a ∧ ¬ ∃ b, (constrainedAfter sem).next a b) :=\n\
             \x20 (model sem).admitted_deadlock_preserved\n\
             #print axioms constrained_certificate\n\
             #print axioms constrained_optimization_correct\n\
             #print axioms constrained_init_counterexample_lifts\n\
             #print axioms constrained_step_counterexample_lifts\n\
             #print axioms admitted_deadlock_preserved\n",
        );
    } else {
        out.push_str(
            "def constrainedBefore := (model sem).constrainedConcrete\n\
             def constrainedAfter := (model sem).constrainedReduced\n",
        );
        if include_erasure_cert {
            out.push_str(
                "def constrainedIntermediate := (model sem).erased.constrainedConcrete\n\
                 theorem erasure_constrained_certificate :\n\
                 \x20 ConstrainedCertificate (constrainedBefore sem) (constrainedIntermediate sem) (erase sem) :=\n\
                 \x20 (model sem).erasure_constrained_certificate\n",
            );
        }
        out.push_str(
            "theorem constrained_certificate :\n\
             \x20 ConstrainedCertificate (constrainedBefore sem) (constrainedAfter sem) (project sem) :=\n\
             \x20 (model sem).constrained_certificate\n\
             theorem constrained_optimization_correct :\n\
             \x20 ConstrainedSafe (constrainedBefore sem) ↔ ConstrainedSafe (constrainedAfter sem) :=\n\
             \x20 TlxOptimization.constrained_safety_iff (constrained_certificate sem)\n\
             theorem constrained_init_counterexample_lifts {a}\n\
             \x20 (ha : (constrainedAfter sem).initial a)\n\
             \x20 (bad : ¬ ((constrainedAfter sem).safe a ∧ (constrainedAfter sem).initSafe a)) :\n\
             \x20 ∃ s, (constrainedBefore sem).initial s ∧ project sem s = a ∧\n\
             \x20   ¬ ((constrainedBefore sem).safe s ∧ (constrainedBefore sem).initSafe s) :=\n\
             \x20 TlxOptimization.constrained_init_counterexample_lifts (constrained_certificate sem) ha bad\n\
             theorem constrained_step_counterexample_lifts {a b}\n\
             \x20 (ha : AdmittedReachable (constrainedAfter sem) a)\n\
             \x20 (hab : (constrainedAfter sem).next a b)\n\
             \x20 (bad : ¬ ((constrainedAfter sem).safe b ∧ (constrainedAfter sem).actionSafe a b)) :\n\
             \x20 ∃ s t, AdmittedReachable (constrainedBefore sem) s ∧ (constrainedBefore sem).next s t ∧\n\
             \x20   project sem s = a ∧ project sem t = b ∧\n\
             \x20   ¬ ((constrainedBefore sem).safe t ∧ (constrainedBefore sem).actionSafe s t) :=\n\
             \x20 TlxOptimization.constrained_step_counterexample_lifts (constrained_certificate sem) ha hab bad\n\
             theorem admitted_deadlock_preserved :\n\
             \x20 (∃ s, AdmittedReachable (constrainedBefore sem) s ∧ ¬ ∃ t, (constrainedBefore sem).next s t) ↔\n\
             \x20 (∃ a, AdmittedReachable (constrainedAfter sem) a ∧ ¬ ∃ b, (constrainedAfter sem).next a b) :=\n\
             \x20 TlxOptimization.constrained_deadlock_iff (constrained_certificate sem)\n",
        );
        if include_erasure_cert {
            out.push_str("#print axioms erasure_constrained_certificate\n");
        }
        out.push_str(
            "#print axioms constrained_certificate\n\
             #print axioms constrained_optimization_correct\n\
             #print axioms constrained_init_counterexample_lifts\n\
             #print axioms constrained_step_counterexample_lifts\n\
             #print axioms admitted_deadlock_preserved\n",
        );
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
            let id = self.next_id;
            self.next_id += 1;
            locals.insert(*l, id);
            self.push(&format!("L{id}"))?;
        }
        Some(())
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
                let &id = locals.get(l)?;
                self.push(&format!("Local({id})"))
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
pub(super) fn canonical_expr_repr(program: &Program, e: &Expr) -> Option<String> {
    canonical_expr_repr_with_limits(program, e, MAX_CANON_WORK, MAX_CANON_BYTES)
}

fn canonical_expr_repr_with_limits(program: &Program, e: &Expr, work: usize, max_bytes: usize) -> Option<String> {
    let mut w = CanonWriter { program, next_id: 0, work, max_bytes, out: String::new() };
    w.fmt_expr(e, &mut std::collections::HashMap::new(), 0)?;
    Some(w.out)
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

fn write_const_subst_fn(body: &mut String, fn_name: &str, vals: &[&str]) {
    use std::fmt::Write;
    writeln!(body, "def {fn_name} (i : Fin ConstSubstCount) : String :=").unwrap();
    write_const_subst_tree(body, vals, 0, vals.len(), 2);
}

/// When zero-arity `CONSTANT C <- target` substitutions were actually expanded
/// by the normalizer into the emitted model, independently compute each declared
/// binding's canonical HIR from `cfg` + `program`, verify it matches the
/// normalizer's recorded expansion (failing closed `None` on any mismatch or
/// unsupported binding count), append the Lean binding-agreement and
/// premise-free certificate-lifting theorems, and close `TlxOptimization.<namespace>` once.
fn attach_const_subst_obligation(
    program: &Program,
    cfg: &Config,
    expanded_substs: &std::collections::BTreeMap<ConstId, String>,
    declare: impl Fn(ConstId) -> Option<String>,
    cert: OpenCert,
) -> Option<String> {
    use std::fmt::Write;
    let OpenCert { mut body, namespace, constrained } = cert;
    if expanded_substs.len() > MAX_CERT_CONST_SUBSTS {
        return None;
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
        write_const_subst_fn(&mut body, "constSubstConst", &names);
        write_const_subst_fn(&mut body, "constSubstTarget", &targets);
        write_const_subst_fn(&mut body, "constSubstDeclared", &declared);
        write_const_subst_fn(&mut body, "constSubstExpanded", &expanded);
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

/// Generate a connected Lean symmetry certificate for a disjoint product of full
/// permutation groups. Prefers the specialized keyed-state IR, then falls back
/// to the generic recursive equivariant value & expression IR, and finally to
/// certified choice-irrelevant symmetry when `CHOOSE` expressions are present.
pub fn symmetry_certificate(
    program: &Program,
    cfg: &Config,
    init: &Expr,
    next: &Expr,
    observations: &[Expr],
    groups: &[Vec<String>],
) -> Option<String> {
    symmetry_certificate_with_spec(program, cfg, init, next, CheckSpec::invariants_only(observations), groups)
}

/// Generate a connected Lean symmetry certificate covering invariants, init properties,
/// constraints, action constraints, and action properties.
pub fn symmetry_certificate_with_spec(
    program: &Program,
    cfg: &Config,
    init: &Expr,
    next: &Expr,
    spec: CheckSpec<'_>,
    groups: &[Vec<String>],
) -> Option<String> {
    keyed::symmetry_certificate_with_spec(program, cfg, init, next, spec, groups)
        .or_else(|| equiv_sym::symmetry_certificate_with_spec(program, cfg, init, next, spec, groups))
        .or_else(|| choose_sym::choose_symmetry_certificate_with_spec(program, cfg, init, next, spec, groups))
}

/// Certify unobserved-variable erasure followed by symmetry for the exact
/// installed retained-variable tuple, preferring `ErasedKeyedCertificate` and
/// falling back to `ErasedEquivCertificate`.
pub fn symmetry_projection_certificate(
    program: &Program,
    cfg: &Config,
    init: &Expr,
    next: &Expr,
    observations: &[Expr],
    groups: &[Vec<String>],
    view: &Expr,
) -> Option<String> {
    symmetry_projection_certificate_with_spec(program, cfg, init, next, CheckSpec::invariants_only(observations), groups, view)
}

/// Certify unobserved-variable erasure followed by symmetry covering invariants,
/// init properties, constraints, action constraints, and action properties.
pub fn symmetry_projection_certificate_with_spec(
    program: &Program,
    cfg: &Config,
    init: &Expr,
    next: &Expr,
    spec: CheckSpec<'_>,
    groups: &[Vec<String>],
    view: &Expr,
) -> Option<String> {
    keyed::symmetry_projection_certificate_with_spec(program, cfg, init, next, spec, groups, view)
        .or_else(|| equiv_sym::symmetry_projection_certificate_with_spec(program, cfg, init, next, spec, groups, view))
}

/// Validate that `view` is a strictly ascending retained-variable tuple and
/// return `(retained, omitted)` with `!omitted.is_empty()`.
pub(in crate::optimize::phase) fn parse_retained_view(program: &Program, view: &Expr) -> Option<(Vec<VarId>, Vec<VarId>)> {
    let ExprKind::Tuple(values) = &*view.kind else { return None };
    let retained = values.iter().map(|e| variable(e, false)).collect::<Option<Vec<_>>>()?;
    if retained.windows(2).any(|pair| pair[0].0 >= pair[1].0) || retained.iter().any(|v| v.idx() >= program.vars.len()) {
        return None;
    }
    let omitted: Vec<_> = (0..program.vars.len()).map(|i| VarId(i as u32)).filter(|v| !retained.contains(v)).collect();
    (!omitted.is_empty()).then_some((retained, omitted))
}

use tlx_front::cfg::Config;

use crate::{builtins::Builtin as B, hir::*, Program};

use domain::{Domain, Domains};

/// A checked state-key projection and labels for the information it forgets.
pub struct FieldProjection {
    pub view: Expr,
    pub fields: Vec<String>,
    /// Generated certificate for the supported rule IR, never implicitly verified.
    pub certificate: Option<String>,
    /// When present, replaces the identity VIEW with a structural runtime key.
    pub ordered: Option<OrderedPlan>,
}

/// Derive one field projection. An unknown transfer, observation, effect or
/// exhausted analysis budget cannot authorize dropping information. The caller
/// supplies all observations, excludes overrides and liveness, and checks
/// equivariance before composing the result with symmetry.
pub fn phase_projection(program: &Program, cfg: &Config, init: &Expr, next: &Expr, observations: &[Expr]) -> Option<FieldProjection> {
    phase_projection_with_spec(program, cfg, init, next, CheckSpec::invariants_only(observations))
}

/// Derive one field projection covering invariants, state constraints, and init properties.
pub fn phase_projection_with_spec(
    program: &Program,
    cfg: &Config,
    init: &Expr,
    next: &Expr,
    spec: CheckSpec<'_>,
) -> Option<FieldProjection> {
    if !cfg_constants_supported(program, cfg) {
        return None;
    }
    let mut expand = normalize::Normalizer::with_config(program, cfg);
    let initial = branches(&expand.root(init)?)?;
    let steps = branches(&expand.root(next)?)?;
    let norm = spec.try_map(|e| expand.root(e))?;
    let norm_spec = norm.as_spec();
    let domains = Domains::infer(program, cfg, &initial, &steps)?;
    let mut best: Option<(FieldProjection, Option<OpenCert>)> = None;
    for (i, d) in domains.vars.iter().enumerate() {
        let fields = match d {
            Domain::Record(fs) => fs,
            Domain::Function(keys, range) if !keys.is_empty() => {
                let Domain::Record(fs) = &**range else { continue };
                fs
            }
            _ => continue,
        };
        if fields.len() > 32 {
            continue;
        }
        for (control, values) in fields {
            let Some(phases) = values.atoms() else { continue };
            if phases.is_empty()
                || phases.len() > 32
                || !domain::compatible(phases)
                || phases.iter().any(|p| domains.atom_expr(p, init.span).is_none())
            {
                continue;
            }
            if let Some((projection, cert)) =
                liveness::derive(program, &domains, VarId(i as u32), control, phases, (&initial, &steps), norm_spec)
            {
                // A Boolean flag can be a valid but unhelpful control field.
                // Prefer certified candidates, then more forgotten fields;
                // the proof is independent of this selection heuristic.
                if best
                    .as_ref()
                    .is_none_or(|(old, old_cert)| (cert.is_some(), projection.fields.len()) > (old_cert.is_some(), old.fields.len()))
                {
                    best = Some((projection, cert));
                }
            }
        }
    }
    let (mut p, cert) = best?;
    if spec.is_constrained() && !sym_totality::check_projection_observations_total(program, cfg, init, next, spec) {
        return None;
    }
    if let Some(c) = cert {
        p.certificate = Some(expand.attach_const_subst(c)?);
    }
    Some(p)
}

#[derive(Clone)]
struct Branch {
    bounds: Vec<Bound>,
    terms: Vec<Expr>,
}

fn branches(e: &Expr) -> Option<Vec<Branch>> {
    split_branches(e, false)
}

pub(in crate::optimize::phase) fn branches_with_if(e: &Expr) -> Option<Vec<Branch>> {
    split_branches(e, true)
}

fn split_branches(e: &Expr, split_if: bool) -> Option<Vec<Branch>> {
    fn split(e: &Expr, split_if: bool, remaining: &mut usize, depth: usize) -> Option<Vec<Branch>> {
        if *remaining == 0 || depth >= 128 {
            return None;
        }
        *remaining -= 1;
        match &*e.kind {
            ExprKind::Or(es) => {
                let mut out = Vec::new();
                for e in es {
                    out.extend(split(e, split_if, remaining, depth + 1)?);
                    if out.len() > 512 {
                        return None;
                    }
                }
                Some(out)
            }
            ExprKind::And(es) => {
                let mut out = vec![Branch { bounds: vec![], terms: vec![] }];
                for e in es {
                    let alternatives = split(e, split_if, remaining, depth + 1)?;
                    if out.len().saturating_mul(alternatives.len()) > 512 {
                        return None;
                    }
                    let mut combined = Vec::new();
                    for a in &out {
                        for b in &alternatives {
                            if a.terms.len() + b.terms.len() > 512 || a.bounds.len() + b.bounds.len() > 128 {
                                return None;
                            }
                            let mut branch = a.clone();
                            branch.bounds.extend(b.bounds.iter().cloned());
                            branch.terms.extend(b.terms.iter().cloned());
                            combined.push(branch);
                        }
                    }
                    out = combined;
                }
                Some(out)
            }
            ExprKind::Quant { kind: QuantKind::Exists, bounds, body } => {
                let mut out = split(body, split_if, remaining, depth + 1)?;
                for b in &mut out {
                    if bounds.len() + b.bounds.len() > 128 {
                        return None;
                    }
                    let mut combined = bounds.clone();
                    combined.append(&mut b.bounds);
                    b.bounds = combined;
                }
                Some(out)
            }
            ExprKind::If { cond, then, els } if split_if => {
                let mut left = split(then, split_if, remaining, depth + 1)?;
                let mut right = split(els, split_if, remaining, depth + 1)?;
                let neg = Expr::new(ExprKind::Builtin { op: B::Not, args: vec![cond.clone()] }, cond.span);
                for b in &mut left {
                    b.terms.insert(0, cond.clone());
                }
                for b in &mut right {
                    b.terms.insert(0, neg.clone());
                }
                left.extend(right);
                if left.len() > 512 {
                    return None;
                }
                Some(left)
            }
            _ => Some(vec![Branch { bounds: vec![], terms: vec![e.clone()] }]),
        }
    }
    split(e, split_if, &mut 100_000, 0)
}

fn variable(e: &Expr, primed: bool) -> Option<VarId> {
    let e = if primed {
        let ExprKind::Builtin { op: B::Prime, args } = &*e.kind else { return None };
        if args.len() != 1 {
            return None;
        }
        &args[0]
    } else {
        e
    };
    if let ExprKind::Var(v) = &*e.kind {
        Some(*v)
    } else {
        None
    }
}

fn unchanged(e: &Expr, v: VarId) -> usize {
    match &*e.kind {
        ExprKind::Var(x) => usize::from(*x == v),
        ExprKind::Tuple(es) => es.iter().map(|e| unchanged(e, v)).sum(),
        _ => 0,
    }
}

fn collect_unchanged_vars(e: &Expr, out: &mut Vec<VarId>) {
    match &*e.kind {
        ExprKind::Var(x) => out.push(*x),
        ExprKind::Tuple(es) => es.iter().for_each(|x| collect_unchanged_vars(x, out)),
        _ => {}
    }
}

fn mentions_phase_var(e: &Expr, primed: bool) -> bool {
    match &*e.kind {
        ExprKind::Var(_) => !primed,
        ExprKind::Builtin { op: B::Prime | B::Unchanged, args } => primed && args.iter().any(|a| mentions_phase_var(a, false)),
        ExprKind::Builtin { op: B::Enabled, .. } => false,
        _ => {
            let mut found = false;
            crate::visit::children(e, &mut |c| found |= mentions_phase_var(c, primed));
            found
        }
    }
}

fn collect_phase_vars(e: &Expr, primed: bool, out: &mut std::collections::BTreeSet<VarId>) {
    match &*e.kind {
        ExprKind::Var(v) if !primed => {
            out.insert(*v);
        }
        ExprKind::Builtin { op: B::Prime | B::Unchanged, args } if primed => {
            for a in args {
                collect_phase_vars(a, false, out);
            }
        }
        ExprKind::Builtin { op: B::Enabled, .. } => {}
        _ => crate::visit::children(e, &mut |c| collect_phase_vars(c, primed, out)),
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum GroundState {
    Visiting,
    Grounded(bool),
}

struct BranchBindings {
    primed: bool,
    single_eq: std::collections::HashMap<VarId, (usize, Expr)>,
    single_rev_eq: std::collections::HashMap<VarId, (usize, Expr)>,
    first_membership: std::collections::HashMap<VarId, usize>,
    state: std::cell::RefCell<std::collections::HashMap<VarId, GroundState>>,
}

impl BranchBindings {
    fn new(branch: &Branch, primed: bool) -> Self {
        let mut eq_counts: std::collections::HashMap<VarId, usize> = std::collections::HashMap::new();
        let mut rev_counts: std::collections::HashMap<VarId, usize> = std::collections::HashMap::new();
        let mut single_eq = std::collections::HashMap::new();
        let mut single_rev_eq = std::collections::HashMap::new();
        let mut first_membership = std::collections::HashMap::new();
        let mut unch = Vec::new();
        for (idx, e) in branch.terms.iter().enumerate() {
            match &*e.kind {
                ExprKind::Builtin { op: B::In | B::SubsetEq, args } if args.len() == 2 => {
                    if let Some(v) = variable(&args[0], primed) {
                        first_membership.entry(v).or_insert(idx);
                    }
                }
                ExprKind::Builtin { op: B::Eq, args } if args.len() == 2 => {
                    let lhs_v = variable(&args[0], primed);
                    let rhs_v = variable(&args[1], primed);
                    if let Some(v) = lhs_v {
                        let c = eq_counts.entry(v).or_insert(0);
                        *c += 1;
                        if *c == 1 {
                            single_eq.insert(v, (idx, args[1].clone()));
                        } else {
                            single_eq.remove(&v);
                        }
                    }
                    if let Some(v) = rhs_v {
                        if lhs_v != Some(v) {
                            let rc = rev_counts.entry(v).or_insert(0);
                            *rc += 1;
                            if *rc == 1 {
                                single_rev_eq.insert(v, (idx, args[0].clone()));
                            } else {
                                single_rev_eq.remove(&v);
                            }
                        }
                    }
                }
                ExprKind::Builtin { op: B::Unchanged, args } if primed && args.len() == 1 => {
                    unch.clear();
                    collect_unchanged_vars(&args[0], &mut unch);
                    for &v in &unch {
                        let c = eq_counts.entry(v).or_insert(0);
                        *c += 1;
                        if *c == 1 {
                            single_eq.insert(v, (idx, Expr::new(ExprKind::Var(v), e.span)));
                        } else {
                            single_eq.remove(&v);
                        }
                    }
                }
                _ => {}
            }
        }
        Self { primed, single_eq, single_rev_eq, first_membership, state: std::cell::RefCell::new(std::collections::HashMap::new()) }
    }

    fn has_earlier_membership(&self, v: VarId, limit_idx: usize) -> bool {
        self.first_membership.get(&v).is_some_and(|&first| first < limit_idx)
    }

    fn var_is_grounded(&self, u: VarId, state: &mut std::collections::HashMap<VarId, GroundState>) -> bool {
        match state.get(&u).copied() {
            Some(GroundState::Grounded(ok)) => return ok,
            Some(GroundState::Visiting) => return false,
            None => {}
        }
        state.insert(u, GroundState::Visiting);
        let ok = match self.single_eq.get(&u) {
            Some((_, u_rhs)) if !mentions_phase_var(u_rhs, self.primed) => true,
            Some((idx, u_rhs)) if !self.has_earlier_membership(u, *idx) => {
                let mut deps = std::collections::BTreeSet::new();
                collect_phase_vars(u_rhs, self.primed, &mut deps);
                deps.into_iter().all(|w| self.var_is_grounded(w, state))
            }
            _ => self.first_membership.contains_key(&u),
        };
        state.insert(u, GroundState::Grounded(ok));
        ok
    }

    fn get(&self, v: VarId) -> Option<Expr> {
        let (idx, rhs) = self.single_eq.get(&v)?;
        if mentions_phase_var(rhs, self.primed)
            && (self.has_earlier_membership(v, *idx) || !self.var_is_grounded(v, &mut self.state.borrow_mut()))
        {
            return None;
        }
        Some(rhs.clone())
    }

    fn get_or_reversed(&self, v: VarId) -> Option<Expr> {
        self.get(v).or_else(|| {
            let (idx, lhs) = self.single_rev_eq.get(&v)?;
            if mentions_phase_var(lhs, self.primed) || self.has_earlier_membership(v, *idx) {
                return None;
            }
            Some(lhs.clone())
        })
    }
}

fn binding(branch: &Branch, v: VarId, primed: bool) -> Option<Expr> {
    BranchBindings::new(branch, primed).get(v)
}

// Bound declarations, even unused ones, must not capture inserted inputs.
pub(super) fn max_local(e: &Expr) -> u32 {
    let mut max = 0;
    let mut ids = |ids: &[LocalId]| {
        for id in ids {
            max = max.max(id.0);
        }
    };
    match &*e.kind {
        ExprKind::Local(id) => ids(&[*id]),
        ExprKind::Quant { bounds, .. } | ExprKind::FnConstruct { bounds, .. } | ExprKind::SetMap { bounds, .. } => {
            for b in bounds {
                ids(b.vars.locals());
            }
        }
        ExprKind::SetFilter { bound, .. } => ids(bound.vars.locals()),
        ExprKind::Choose { vars, .. } => ids(vars.locals()),
        ExprKind::Lambda { params, .. } => ids(params),
        ExprKind::QuantUnbounded { vars, .. } | ExprKind::TemporalQuant { vars, .. } => ids(vars),
        _ => {}
    }
    crate::visit::children(e, &mut |e| max = max.max(max_local(e)));
    max
}

#[cfg(test)]
mod const_subst_tests {
    use super::*;
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
            |c| normalize::Normalizer::expand_declared_const_subst(&program, &cfg, c),
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
            |c| normalize::Normalizer::expand_declared_const_subst(&program, &cfg, c),
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
            |c| normalize::Normalizer::expand_declared_const_subst(&program, &cfg, c),
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
            |c| normalize::Normalizer::expand_declared_const_subst(&program, &cm, c),
            dummy_cert.clone(),
        )
        .is_none());
        assert!(attach_const_subst_obligation(
            &program,
            &ct,
            &BTreeMap::from([(cid, repr_many.clone())]),
            |c| normalize::Normalizer::expand_declared_const_subst(&program, &ct, c),
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
            |c| normalize::Normalizer::expand_declared_const_subst(&program, &cm, c),
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

        // Unbound locals and un-normalized raw HIR forms must return `None`.
        assert!(canonical_expr_repr(&program, &Expr::new(ExprKind::Local(LocalId(42)), s1)).is_none());
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
            |c| normalize::Normalizer::expand_declared_const_subst(&program, &cfg, c),
            cert.clone(),
        )
        .expect("MAX_CERT_CONST_SUBSTS bindings should emit balanced tree obligation");
        assert!(ok.contains("intro i; rfl"));

        let over_cap: BTreeMap<ConstId, String> = (0..count).map(|i| (ConstId(i as u32), "Num(1)".into())).collect();
        assert!(attach_const_subst_obligation(
            &program,
            &cfg,
            &over_cap,
            |c| normalize::Normalizer::expand_declared_const_subst(&program, &cfg, c),
            cert,
        )
        .is_none());
    }
}
