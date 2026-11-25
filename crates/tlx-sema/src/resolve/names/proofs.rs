//! SANY's checks on theorems, proofs and USE / HIDE: the scopes of NEW,
//! TAKE, PICK, DEFINE and step names, facts and DEF clauses, labels, and
//! RECURSIVE sections.

use std::sync::Arc;

use tlx_front::ast::{self, Span};

use super::{proof_origin, simple_entry, Checker, Entry, Kind, ModIdx, NameScope, Origin};

const HIDE_FACT: &str = "The only expression allowed as a fact in a HIDE is \nthe name of a theorem, assumption, or step.";
const NESTED_LABEL: &str = "Label not allowed within scope of declaration in nested ASSUME/PROVE.";
const NOT_A_DEF: &str = "DEF clause entry should describe a defined operator.";

/// Saved label state (see `Checker::enter_def`).
type LabelState = (usize, Option<&'static str>);

impl Checker<'_> {
    /// `Module::proofs[j]` of module `m`; `pending`: the RECURSIVE
    /// declarations not yet defined.
    pub(super) fn proof_unit(&mut self, sc: &mut NameScope, m: ModIdx, j: usize, pu: &ast::ProofUnit, pending: &[(Arc<str>, Span)]) {
        match pu {
            ast::ProofUnit::UseOrHide(u) => {
                if !pending.is_empty() {
                    self.error(u.span, "A USE or HIDE may not appear within a recursive definition section.".into());
                }
                self.use_or_hide(sc, u);
            }
            ast::ProofUnit::Theorem { name, stmt, proof, span } => {
                // A named theorem with an expression statement is also a
                // `Unit::Theorem`, already checked (and bound).
                let done = name.is_some() && matches!(stmt, ast::Stmt::Expr(_));
                let mark = sc.locals.len();
                if !done {
                    if !pending.is_empty() {
                        self.error(*span, "A THEOREM may not appear within a recursive definition section.".into());
                    }
                    // Labels are allowed in named theorems only.
                    let saved = if name.is_some() { Some(self.enter_def(mark)) } else { None };
                    self.stmt(sc, stmt);
                    if let Some(s) = saved {
                        self.leave_def(s);
                    }
                    // The name is visible in the proof.
                    if let Some(n) = name {
                        let mname = self.mod_name(m);
                        self.bind_own(sc, &n.name, simple_entry(Kind::Theorem, 0, n.span, proof_origin(m, j), &mname), false);
                    }
                }
                if let Some(p) = proof {
                    self.proof(sc, p);
                }
                sc.locals.truncate(mark);
            }
        }
    }

    /// Start checking a definition-like body (labels allowed, their
    /// parameters bound by `locals[mark..]`).
    fn enter_def(&mut self, mark: usize) -> LabelState {
        let saved = (self.label_mark, self.label_ban);
        self.label_mark = mark;
        self.label_ban = None;
        self.label_levels.push(Vec::new());
        saved
    }

    fn leave_def(&mut self, saved: LabelState) {
        self.label_levels.pop();
        (self.label_mark, self.label_ban) = saved;
    }

    /// Bind an identifier introduced by NEW, TAKE or PICK.
    fn bind_new(&mut self, sc: &mut NameScope, id: &ast::Ident, arity: usize) {
        let e = simple_entry(Kind::Constant, arity, id.span, Origin::Local, &self.mod_name(self.cur_mod));
        if let Some(old) = self.lookup(sc, &id.name).cloned() {
            self.conflict(&id.name, &old, &e);
        }
        sc.locals.push((id.name.clone(), e));
    }

    /// A statement; the NEW declarations of an ASSUME/PROVE stay bound.
    fn stmt(&mut self, sc: &mut NameScope, s: &ast::Stmt) {
        match s {
            ast::Stmt::Expr(e) => self.expr(sc, e),
            ast::Stmt::AssumeProve(ap) => self.assume_prove(sc, ap, false),
        }
    }

    fn assume_prove(&mut self, sc: &mut NameScope, ap: &ast::AssumeProve, nested: bool) {
        let saved = self.label_ban;
        for a in &ap.assumes {
            match a {
                ast::Assumption::Expr(e) => self.expr(sc, e),
                ast::Assumption::New(nd) => {
                    if let Some(s) = &nd.set {
                        self.expr(sc, s);
                    }
                    self.bind_new(sc, &nd.decl.name, nd.decl.arity);
                    if nested && self.label_ban.is_none() {
                        self.label_ban = Some(NESTED_LABEL);
                    }
                }
                ast::Assumption::AssumeProve(inner) => {
                    let mark = sc.locals.len();
                    self.assume_prove(sc, inner, true);
                    sc.locals.truncate(mark);
                }
            }
        }
        self.expr(sc, &ap.prove);
        self.label_ban = saved;
    }

    fn binders(&mut self, sc: &mut NameScope, b: &ast::Binders) {
        match b {
            ast::Binders::Bounded(bs) => {
                for x in bs {
                    self.expr(sc, &x.set);
                }
                for x in bs {
                    let vs = match &x.vars {
                        ast::BoundVars::Many(v) | ast::BoundVars::Tuple(v) => v,
                    };
                    for v in vs {
                        self.bind_new(sc, v, 0);
                    }
                }
            }
            ast::Binders::Unbounded(vs) => {
                for v in vs {
                    self.bind_new(sc, v, 0);
                }
            }
        }
    }

    fn proof(&mut self, sc: &mut NameScope, p: &ast::Proof) {
        match p {
            ast::Proof::Leaf { by, .. } => {
                if let Some(b) = by {
                    self.use_body(sc, b, false);
                }
            }
            ast::Proof::Steps(steps) => {
                let mark = sc.locals.len();
                for st in steps {
                    self.step(sc, st);
                }
                sc.locals.truncate(mark);
            }
        }
    }

    fn step(&mut self, sc: &mut NameScope, st: &ast::Step) {
        use ast::StepKind as S;
        let mark = sc.locals.len();
        // Names that stay bound for the rest of the proof.
        let mut keep: Vec<(Arc<str>, Entry)> = Vec::new();
        let saved = self.enter_def(mark);
        let what = match &st.kind {
            S::Assert(_) | S::Define(_) | S::UseOrHide(_) | S::Instance(_) => None,
            S::Suffices(_) => Some("SUFFICES"),
            S::Have(_) => Some("HAVE"),
            S::Witness(_) => Some("WITNESS"),
            S::Take(_) => Some("TAKE"),
            S::Case(_) => Some("CASE"),
            S::Pick(..) => Some("PICK"),
            S::Qed => Some("QED step"),
        };
        match &st.kind {
            S::Assert(s) => {
                self.stmt(sc, s);
                self.leave_def(saved);
                self.sub_proof(sc, st);
                sc.locals.truncate(mark);
            }
            S::Suffices(s) => {
                // The NEW declarations are visible in the rest of the proof,
                // not in the proof of the SUFFICES step.
                self.stmt(sc, s);
                self.leave_def(saved);
                keep = sc.locals.split_off(mark);
                self.sub_proof(sc, st);
            }
            S::Pick(b, e) => {
                self.binders(sc, b);
                self.expr(sc, e);
                self.leave_def(saved);
                keep = sc.locals.split_off(mark);
                self.sub_proof(sc, st);
            }
            S::Case(e) => {
                self.expr(sc, e);
                self.leave_def(saved);
                self.sub_proof(sc, st);
            }
            S::Qed => {
                self.leave_def(saved);
                self.sub_proof(sc, st);
            }
            S::Have(e) => {
                self.expr(sc, e);
                self.leave_def(saved);
            }
            S::Witness(es) => {
                for e in es {
                    self.expr(sc, e);
                }
                self.leave_def(saved);
            }
            S::Take(b) => {
                self.binders(sc, b);
                self.leave_def(saved);
            }
            S::UseOrHide(u) => {
                self.leave_def(saved);
                self.use_or_hide(sc, u);
            }
            S::Define(units) => {
                self.leave_def(saved);
                let mname = self.mod_name(self.cur_mod);
                for u in units {
                    match u {
                        ast::Unit::OpDef(od) => {
                            self.op_def(sc, od);
                            self.bind_own(sc, &od.name.name, super::op_def_entry(od, Origin::Local, &mname), true);
                        }
                        ast::Unit::FnDef(fd) => {
                            self.bind_own(sc, &fd.name.name, super::fn_def_entry(fd, Origin::Local, &mname), true);
                            self.fn_def(sc, fd);
                        }
                        ast::Unit::Instance(inst) => self.proof_instance(sc, inst),
                        _ => {}
                    }
                }
            }
            S::Instance(inst) => {
                self.leave_def(saved);
                self.proof_instance(sc, inst);
            }
        }
        sc.locals.extend(keep);
        // A step name `<1>a` (not an unnamed `<1>`).
        if !st.id.name.ends_with('>') {
            let e = simple_entry(Kind::Step(what), 0, st.id.span, Origin::Local, &self.mod_name(self.cur_mod));
            sc.locals.push((st.id.name.clone(), e));
        }
    }

    fn sub_proof(&mut self, sc: &mut NameScope, st: &ast::Step) {
        if let Some(p) = &st.proof {
            self.proof(sc, p);
        }
    }

    fn proof_instance(&mut self, sc: &mut NameScope, inst: &ast::Instance) {
        let m = self.cur_mod;
        self.instance(sc, m, inst);
        if let Some(n) = &inst.name {
            let e = super::instance_entry(inst, n.span, Origin::Local, &self.mod_name(m));
            self.bind_own(sc, &n.name, e, true);
        }
    }

    fn use_or_hide(&mut self, sc: &mut NameScope, u: &ast::UseOrHide) {
        self.use_body(sc, &u.body, u.hide);
    }

    /// The facts and DEF clause of a USE, HIDE or BY.
    fn use_body(&mut self, sc: &mut NameScope, b: &ast::UseBody, hide: bool) {
        for f in &b.facts {
            let ast::Fact::Expr(e) = f else { continue };
            match &*e.kind {
                // The name of a fact (a step name can be used as a fact
                // whatever the step is).
                ast::ExprKind::OpAppl { prefix, name, args } if args.is_empty() => {
                    if prefix.is_empty() {
                        let found = self.use_name(sc, name);
                        if hide && found.is_some_and(|f| !matches!(f.kind, Kind::Theorem | Kind::Step(_))) {
                            self.error(e.span, HIDE_FACT.into());
                        }
                    } else {
                        self.prefix_args(sc, prefix);
                        self.use_name(sc, &prefix[0].name);
                    }
                }
                _ => {
                    if hide {
                        self.error(e.span, HIDE_FACT.into());
                    }
                    self.expr(sc, e);
                }
            }
        }
        for d in &b.defs {
            let ast::Fact::Expr(e) = d else { continue };
            let ast::ExprKind::OpAppl { prefix, name, args } = &*e.kind else { continue };
            if !args.is_empty() {
                self.error(e.span, NOT_A_DEF.into());
            } else if !prefix.is_empty() {
                self.prefix_args(sc, prefix);
                self.use_name(sc, &prefix[0].name);
            } else if let Some(found) = self.use_name(sc, name) {
                let def = match found.kind {
                    Kind::Op | Kind::Fn(_) | Kind::Builtin | Kind::Instance => true,
                    Kind::Theorem => !name.name.starts_with('<'),
                    Kind::Constant | Kind::Variable | Kind::Param | Kind::Step(_) => false,
                };
                if !def {
                    self.error(e.span, NOT_A_DEF.into());
                }
            }
        }
    }
}
