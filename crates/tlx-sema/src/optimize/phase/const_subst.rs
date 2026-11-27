//! `.cfg` constant-substitution resolution, the canonical HIR writer, and the
//! Lean obligations that connect declared substitutions to their expansions.

use tlx_front::cfg::Config;

use crate::hir::{Bound, BoundVars, ConstId, DefId, ExceptKey, Expr, ExprKind, LocalId, RootSymbol, Span};
use crate::{builtins::Builtin as B, Program};

use super::cert::OpenCert;

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
pub(in crate::optimize::phase) fn canonical_expr_repr(program: &Program, e: &Expr) -> Option<String> {
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
pub(in crate::optimize::phase) fn attach_const_subst_obligation(
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
