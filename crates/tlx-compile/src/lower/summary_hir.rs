//! Environment-aware fallback dependency facts. Compiled calls are handled by summary.
use super::*;
use crate::binding::{Flow, Policy, Scope, State};
use crate::enc::mixed::Reads;
use std::collections::HashSet;
use tlx_sema::builtins::Builtin;
use tlx_sema::hir::{ConstId, ExprKind as H, LocalId};

pub(super) struct FallbackFacts {
    pub reads: Option<Reads>,
    pub enabled: bool,
    pub operator_args: bool,
    pub recursive: bool,
}

/// The read-set policy of the shared environment-aware walk (`crate::binding`):
/// which state variables an interpreter fallback can read (current and next
/// state), whether it reaches an `ENABLED`, whether it passes operator
/// arguments, and whether a definition recurred. It counts structural depth
/// (`depth > 64` gives up) and replaces the environment at a closure or a
/// definition body (a single current environment).
struct ReadPolicy {
    reads: Reads,
    /// (definition, primed) pairs already walked.
    seen: HashSet<(hir::DefId, bool)>,
    /// Whether the reads are still exact (false: no read set is reported).
    known: bool,
    enabled: bool,
    operator_args: bool,
    recursive: bool,
    /// (definition, primed) pairs on the current path: a repeat is recursion.
    active: HashSet<(hir::DefId, bool)>,
}

impl ReadPolicy {
    fn add(&mut self, v: u32, primed: bool) {
        let set = if primed { &mut self.reads.next } else { &mut self.reads.cur };
        if !set.contains(&v) {
            set.push(v);
        }
    }
}

impl Policy for ReadPolicy {
    fn node(&mut self, s: &mut State<'_>, e: &hir::Expr, depth: usize) -> Flow {
        if !self.known || depth > 64 {
            self.known = false;
            return Flow::Done;
        }
        self.operator_args |= matches!(&*e.kind, H::OpArg(_) | H::Lambda { .. } | H::Apply { op: OpRef::Param(_), .. });
        if let H::Var(v) = &*e.kind {
            self.add(v.idx() as u32, s.primed());
        }
        Flow::Children
    }

    fn builtin(&mut self, s: &mut State<'_>, op: Builtin, _args: &[hir::Expr], _depth: usize) -> Flow {
        match op {
            Builtin::Prime => Flow::PrimedArgs,
            Builtin::Unchanged => Flow::BothArgs,
            // Its next state is local; its current-state reads are not
            // tracked separately.
            Builtin::Enabled => {
                self.enabled = true;
                self.known = false;
                Flow::Done
            }
            // A builtin the cfg replaces by a definition: not followed.
            _ if s.ip.is_builtin_overridden(op) => {
                self.known = false;
                Flow::Done
            }
            _ => Flow::Children,
        }
    }

    fn child_depth(&self, depth: usize) -> usize {
        depth + 1
    }

    fn def(&mut self, s: &mut State<'_>, d: hir::DefId) -> bool {
        let key = (d, s.primed());
        if self.active.contains(&key) {
            self.recursive = true;
        }
        if !self.seen.insert(key) {
            return false;
        }
        self.active.insert(key);
        true
    }

    fn def_done(&mut self, s: &mut State<'_>, d: hir::DefId) {
        self.active.remove(&(d, s.primed()));
    }

    fn pending_def(&mut self, _s: &mut State<'_>, _d: hir::DefId) {
        self.known = false;
    }

    fn local(&mut self, _s: &mut State<'_>, _l: LocalId, depth: usize) -> bool {
        if depth > 64 {
            self.known = false;
            return false;
        }
        true
    }

    fn bound_operator(&mut self, _s: &mut State<'_>, _l: LocalId) {
        self.operator_args = true;
    }

    /// A constant bound to a definition by the cfg (`C <- Def`).
    fn constant(&mut self, s: &mut State<'_>, c: ConstId, _depth: usize) {
        if let Some(d) = s.ip.const_def(c) {
            s.def(self, d);
        }
    }

    /// A constant in operator position: the cfg may bind it to a definition,
    /// to a builtin, or to neither (then the reads are unknown).
    fn op_const(&mut self, s: &mut State<'_>, c: ConstId, _depth: usize) {
        match s.ip.const_op_ref(c) {
            Some(OpRef::Def(d)) => s.def(self, d),
            Some(OpRef::Builtin(_)) => {}
            _ => self.known = false,
        }
    }
}

impl Lowerer<'_> {
    pub(super) fn fallback_facts(&self, e: &Expr) -> FallbackFacts {
        let mut p = ReadPolicy {
            reads: Reads::default(),
            seen: HashSet::new(),
            known: true,
            enabled: false,
            operator_args: false,
            recursive: false,
            active: HashSet::new(),
        };
        if let ExprKind::Interp { expr, deferred, env, .. } = &*e.kind {
            let full_env = crate::binding::bind_deferred(self.ip, env, deferred);
            let mut s = State::new(self.ip, Scope::Single, full_env);
            s.walk(&mut p, expr, 0);
            s.walk_deferred(&mut p, deferred, 0);
        }
        FallbackFacts { reads: p.known.then_some(p.reads), enabled: p.enabled, operator_args: p.operator_args, recursive: p.recursive }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tlx_sema::hir::DefKind;

    pub(super) fn lowerer(model: &tlx_eval::model::InterpModel) -> Lowerer<'_> {
        Lowerer::with_typing(&model.ip, crate::types::Typing::new(Arc::new(tlx_layout::Layout::new(vec![tlx_layout::Shape::Dyn]))))
    }

    pub(super) fn body(model: &tlx_eval::model::InterpModel, name: &str) -> Expr {
        let def = model.ip.prog.defs.iter().find(|d| &*d.name == name).unwrap();
        let DefKind::Op(body) = &def.kind else { panic!("operator") };
        Expr::new(Ty::Bool, ExprKind::Interp { expr: body.clone(), binds: vec![], deferred: vec![], env: Env::default() })
    }

    /// The fallback facts the shared environment-aware walk
    /// (`crate::binding`) must keep: `LET` and recursion, operator
    /// arguments, `'e`/`UNCHANGED` priming and a `CONSTANT` the cfg binds to
    /// a definition.
    #[test]
    fn fallback_facts_cover_let_recursion_operator_arguments_and_overrides() {
        let source = tlx_testkit::module(
            "SummaryHIR",
            r#"
EXTENDS Naturals
VARIABLE x, y
CONSTANT C
RECURSIVE Rec(_)
Rec(n) == IF n = 0 THEN x ELSE Rec(n - 1)
Higher(Op(_)) == Op(x)
Override == y
Main == LET F(n) == Rec(n) IN Higher(LAMBDA n: F(n)) = x
Init == x = 0
Next == x' = x + 1
Live == ENABLED Next
Prime == x' = x /\ y' = y
UnchangedBoth == UNCHANGED <<x, y>>
LetConst == LET K == C IN K = x
"#,
        );
        let model = tlx_testkit::spec::load(
            &source,
            "CONSTANT C <- Override\nINIT Init\nNEXT Next\nINVARIANT Main Live Prime UnchangedBoth LetConst\n",
        );
        let lw = lowerer(&model);
        // The fixtures reach the paths the batch names: LET + recursion +
        // operator arguments, `'e`/`UNCHANGED` priming, and `C <- Override`.
        let facts = |name: &str| lw.fallback_facts(&body(&model, name));
        assert_eq!(facts("Main").reads, Some(Reads { cur: vec![0], next: vec![] }));
        assert!(facts("Main").operator_args && facts("Main").recursive);
        assert_eq!(facts("Prime").reads, Some(Reads { cur: vec![0, 1], next: vec![0, 1] }));
        assert_eq!(facts("UnchangedBoth").reads, Some(Reads { cur: vec![0, 1], next: vec![0, 1] }));
        assert_eq!(facts("LetConst").reads, Some(Reads { cur: vec![1, 0], next: vec![] }));
        assert_eq!(facts("Live").reads, None);
    }

    #[test]
    fn fallback_summary_tracks_recursive_operator_arguments_and_enabled() {
        let source = tlx_testkit::module(
            "SummaryHIR",
            r#"
EXTENDS Naturals
VARIABLE x
RECURSIVE Rec(_)
Rec(n) == IF n = 0 THEN x ELSE Rec(n - 1)
Higher(Op(_)) == Op(x)
Main == LET F(n) == Rec(n) IN Higher(LAMBDA n: F(n)) = x
Init == x = 0
Next == x' = x + 1
Live == ENABLED Next
"#,
        );
        let model = tlx_testkit::spec::load(&source, "INIT Init\nNEXT Next\nINVARIANT Main Live\n");
        let lw = lowerer(&model);
        let main = lw.expression_summary(&body(&model, "Main"));
        assert_eq!(main.reads, Some(Reads { cur: vec![0], next: vec![] }));
        assert!(main.operator_args && main.recursive && !main.unknown);
        let enabled = lw.expression_summary(&body(&model, "Live"));
        assert!(enabled.enabled && enabled.unknown);
        assert_eq!(enabled.reads, None);
        assert!(enabled.context.next.iter().all(|b| !b));
    }

    #[test]
    fn fallback_facts_preserve_scope_across_let_and_track_primed_deferred() {
        let source = tlx_testkit::module(
            "SummaryLetDeferred",
            r#"
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = x
UseLet(Op(_)) == LET y == Op(1) IN y = 2
UsePrimed(a) == a' = 1
"#,
        );
        let model = tlx_testkit::spec::load(&source, "INIT Init\nNEXT Next\n");
        let lw = lowerer(&model);

        // Operator bound in the fallback's `env`, referenced inside a `LET`:
        // `Scope::Single` must NOT wipe `env` when entering `LET y == Op(1)`.
        let use_let = model.ip.prog.defs.iter().find(|d| &*d.name == "UseLet").unwrap();
        let DefKind::Op(use_let_body) = &use_let.kind else { panic!("operator") };
        let op_param = use_let.params[0];
        let lam_param = LocalId(999);
        let lam_body = hir::Expr::new(
            H::Builtin {
                op: Builtin::Plus,
                args: vec![
                    hir::Expr::new(H::Local(lam_param), Default::default()),
                    hir::Expr::new(H::Var(hir::VarId(0)), Default::default()),
                ],
            },
            Default::default(),
        );
        let env = Env::default().bind(
            op_param,
            tlx_eval::env::Binding::Op(tlx_eval::env::OpVal::Lambda {
                params: Arc::from([lam_param]),
                body: lam_body,
                env: Env::default(),
            }),
        );
        let e = Expr::new(Ty::Bool, ExprKind::Interp { expr: use_let_body.clone(), binds: vec![], deferred: vec![], env });
        assert_eq!(lw.fallback_facts(&e).reads, Some(Reads { cur: vec![0], next: vec![] }));

        // Primed `Deferred::Thunk` local must record `reads.next`.
        let use_primed = model.ip.prog.defs.iter().find(|d| &*d.name == "UsePrimed").unwrap();
        let DefKind::Op(use_primed_body) = &use_primed.kind else { panic!("operator") };
        let a_param = use_primed.params[0];
        let deferred = vec![Deferred::Thunk(a_param, hir::Expr::new(H::Var(hir::VarId(0)), Default::default()))];
        let e_primed =
            Expr::new(Ty::Bool, ExprKind::Interp { expr: use_primed_body.clone(), binds: vec![], deferred, env: Env::default() });
        let reads = lw.fallback_facts(&e_primed).reads.expect("reads");
        assert!(reads.next.contains(&0), "primed deferred local must record reads.next: {reads:?}");
    }
}
