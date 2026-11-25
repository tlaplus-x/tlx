//! Module loading and name resolution: surface AST -> HIR.
//!
//! Model (design.md §3.2):
//! - A *context* (`Ctx`) is a substitution environment for module declarations.
//!   The root context maps CONSTANT/VARIABLE declarations to global ids; an
//!   `INSTANCE M WITH ...` creates a child context in which M's declarations
//!   are replaced by the (re-resolved) substitution expressions.
//! - A module's *scope* is computed per (context, module). EXTENDS shares the
//!   context; INSTANCE creates a new one. Modules that declare nothing are
//!   always placed in the root context, so standard modules are resolved once.
//! - Parameterized instances `I(p) == INSTANCE M ...` give every definition in
//!   the instance context extra leading parameters (`Ctx::inst_params`).
//! - Definition bodies are resolved lazily (on first use) and memoized.
//!
//! Submodules:
//! - `modules`: finding, parsing and registering module sources; ASSUMEs;
//! - `scope`: per-(context, module) scopes and instance contexts;
//! - `expr`: resolution of expressions and LET;
//! - `apply`: operator applications, instance-qualified names and
//!   INSTANCE substitution;
//! - `bindings`: the scoped binding-form handlers of `names` and `level`
//!   (labels, quantifiers, CHOOSE, set forms, LET);
//! - `subexpr`: subexpression selectors `D!sel`.

mod apply;
mod arena;
mod bindings;
mod expr;
mod level;
mod modules;
mod names;
mod proof_levels;
mod scope;
mod subexpr;

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use tlx_front::ast::{self, FileId, Span};

use crate::hir::*;
pub use crate::source::ModuleOrigin;
pub use level::CfgLevelError;
use subexpr::SelKey;

#[derive(Clone, Debug)]
pub struct SemaError {
    pub span: Span,
    pub message: String,
    /// The file the error is in, filled in when the error leaves `Program`
    /// (the path as the module was found). `None` for errors that predate any
    /// source file, e.g. an unreadable root module.
    pub file: Option<Arc<PathBuf>>,
}

impl std::fmt::Display for SemaError {
    /// `file:line:col: message`. Errors that predate any source file keep the
    /// bare `line:col: message`.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.file {
            Some(p) => write!(f, "{}:{}:{}: {}", user_path(p), self.span.line, self.span.col, self.message),
            None => write!(f, "{}:{}: {}", self.span.line, self.span.col, self.message),
        }
    }
}

/// The path as the user would recognize it: relative to the current directory
/// when the file is under it, else as the module was found (a `-I` directory,
/// or `<stdlib>/...` for a bundled module).
fn user_path(path: &Path) -> String {
    if let Ok(cwd) = std::env::current_dir() {
        if let Ok(rel) = path.strip_prefix(&cwd) {
            return rel.display().to_string();
        }
        // `current_dir` is physical while the path may be logical (on macOS
        // `/var` vs `/private/var`), so compare resolved paths too.
        if let (Ok(p), Ok(c)) = (path.canonicalize(), cwd.canonicalize()) {
            if let Ok(rel) = p.strip_prefix(&c) {
                return rel.display().to_string();
            }
        }
    }
    let s = path.display().to_string();
    s.strip_prefix("./").map(str::to_string).unwrap_or(s)
}

#[derive(Clone, Debug)]
pub struct SourceFile {
    pub path: PathBuf,
    pub src: Arc<str>,
    pub origin: ModuleOrigin,
    lines: std::sync::OnceLock<crate::source::LineIndex>,
}

impl SourceFile {
    pub fn new(path: PathBuf, src: Arc<str>) -> SourceFile {
        Self::with_origin(path, src, ModuleOrigin::User)
    }

    pub fn with_origin(path: PathBuf, src: Arc<str>, origin: ModuleOrigin) -> SourceFile {
        SourceFile { path, src, origin, lines: std::sync::OnceLock::new() }
    }

    /// The line index of the source (built on first use).
    pub fn lines(&self) -> &crate::source::LineIndex {
        self.lines.get_or_init(|| crate::source::LineIndex::new(&self.src))
    }
}

/// What is wrong with a configuration `<-` substitution (TLC's
/// `SpecProcessor.processSpec` checks; the codes are in the CLI's `out::code`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CfgSubstError {
    /// TLC_CONFIG_RHS_ID_APPEARED_AFTER_LHS_ID: the right-hand side is also
    /// substituted for.
    RhsAppearedAfterLhs(String),
    /// TLC_CONFIG_WRONG_SUBSTITUTION: the right-hand side is not defined.
    WrongSubstitution { lhs: String, rhs: String },
    /// TLC_CONFIG_WRONG_SUBSTITUTION_NUMBER_OF_ARGS.
    WrongNumberOfArgs { lhs: String, rhs: String },
    /// TLC_CONFIG_ID_DOES_NOT_APPEAR_IN_SPEC: the left-hand side is not a
    /// root constant, a root operator definition, or (module-scoped) an
    /// operator definition of the module.
    IdDoesNotAppear(String),
    /// TLC_NO_MODULES: a module the configuration substitutes in is not part
    /// of the specification.
    NoModules(String),
}

/// What is wrong with a name a configuration section refers to (TLC's
/// `SpecProcessor.processConfig` checks).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CfgNameError {
    /// TLC_CONFIG_SPECIFIED_NOT_DEFINED: the spec does not define the name.
    NotDefined { what: &'static str, name: String },
    /// TLC_CONFIG_ID_REQUIRES_NO_ARG: the name takes arguments.
    RequiresNoArg { what: &'static str, name: String },
    /// TLC_CONFIG_ID_HAS_VALUE (an invariant or a specification name), or
    /// TLC_CONFIG_ID_MUST_NOT_BE_CONSTANT (an initial predicate or a
    /// next-state action): the name is a constant with a value.
    IsConstant { what: &'static str, name: String },
    /// TLC_CONFIG_NOT_BOTH_SPEC_AND_INIT: a SPECIFICATION and an INIT/NEXT.
    NotBothSpecAndInit,
}

type ModIdx = usize;
type CtxId = usize;
type ScopeId = usize;

const ROOT_CTX: CtxId = 0;

struct ModInfo {
    name: Arc<str>,
    ast: Arc<ast::Module>,
    std: bool,
    /// Enclosing module of a nested module (whose definitions it can see).
    parent: Option<ModIdx>,
}

struct Ctx {
    /// Accumulated instance parameters (outer instances first).
    inst_params: Vec<(Arc<str>, usize)>,
    subst: Option<SubstInfo>,
    /// The copy of this instance context that the argument of an `ENABLED`
    /// in it is resolved in (`Program::enabled_ctx`): its VARIABLEs are
    /// `ExprKind::InstVar`s (created on first use).
    fresh: Option<CtxId>,
    /// For such a copy: the context it copies.
    copy_of: Option<CtxId>,
    /// A substitution of this (LET) instance refers to names bound in the
    /// enclosing expression: its definitions are evaluated like LET
    /// definitions, in the environment of their use.
    uses_capture: bool,
}

/// The names bound around a `LET I == INSTANCE M ...`, visible to its
/// substitutions.
type Captured = Arc<Vec<(Arc<str>, LocalBinding)>>;

#[derive(Clone)]
struct SubstInfo {
    /// Context/module in which substitution expressions are resolved.
    outer_ctx: CtxId,
    outer_mod: ModIdx,
    /// Number of instance params of the outer context (a prefix of ours).
    outer_inst: usize,
    explicit: HashMap<Arc<str>, ast::Expr>,
    /// The instantiated module and the INSTANCE (for level errors).
    target: ModIdx,
    span: Span,
    /// For an INSTANCE in a LET: the names bound around it.
    captured: Option<Captured>,
}

/// What a module-level name denotes.
#[derive(Clone, Copy, Debug)]
enum Sym {
    Var(VarId),
    Const(ConstId),
    /// Declaration inside an instance context: replaced by its substitution.
    /// `var`: a VARIABLE (rather than a CONSTANT).
    Decl {
        ctx: CtxId,
        arity: usize,
        var: bool,
    },
    Def(DefId),
    Instance(InstId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct InstId(usize);

struct InstInfo {
    /// Context and module containing the INSTANCE definition.
    ctx: CtxId,
    module: ModIdx,
    ast: ast::Instance,
    /// Lazily created context of the instantiated module.
    target: Option<(CtxId, ModIdx)>,
    /// For an INSTANCE in a LET: the names bound around it.
    captured: Option<Captured>,
}

struct Scope {
    names: HashMap<Arc<str>, Sym>,
    exports: HashMap<Arc<str>, Sym>,
}

/// Where a definition's body comes from, for lazy resolution.
struct DefSrc {
    ctx: CtxId,
    module: ModIdx,
    unit: DefUnit,
    state: DefState,
}

#[derive(Clone)]
enum DefUnit {
    Op(ast::OpDef),
    Fn(ast::FnDef),
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum DefState {
    Unresolved,
    InProgress,
    Done,
    /// LET definitions are resolved eagerly in their enclosing environment.
    Local,
}

/// What a name bound inside an expression (`Env::names`) denotes.
#[derive(Clone)]
enum LocalBinding {
    Local(LocalId, usize),
    LetDef(DefId),
    /// An instance parameter bound to an already-resolved 0-ary expression (`J(1)!K`).
    Value(Expr),
    /// An operator-valued instance parameter bound to an already-resolved
    /// operator expression (`OpArg` or `Lambda`) of the declared arity (`> 0`).
    Op(Expr, usize),
    /// `LET I == INSTANCE M ...`
    Instance(InstId),
}

/// Expression-resolution environment.
struct Env {
    ctx: CtxId,
    module: ModIdx,
    /// Resolved expressions for the current context's instance params
    /// (`Local` / `OpArg(Param)` inside a definition body, or arbitrary
    /// resolved expressions forwarded through nested substitutions).
    inst_args: Vec<Expr>,
    names: Vec<(Arc<str>, LocalBinding)>,
    /// Whether `@` is allowed (inside an EXCEPT update value).
    in_except: bool,
    /// The expression being resolved is an argument of an operator (or the
    /// substitution for a declared operator), so it may denote an operator.
    in_arg: bool,
    /// `names[..captured]` are captured from around a LET INSTANCE ...
    captured: usize,
    /// ... and one of them was used.
    used_capture: std::cell::Cell<bool>,
}

impl Env {
    fn new(ctx: CtxId, module: ModIdx) -> Env {
        Env {
            ctx,
            module,
            inst_args: Vec::new(),
            names: Vec::new(),
            in_except: false,
            in_arg: false,
            captured: 0,
            used_capture: std::cell::Cell::new(false),
        }
    }

    /// The innermost local binding of `name`, if any.
    fn local(&self, name: &str) -> Option<&LocalBinding> {
        let i = self.names.iter().rposition(|(n, _)| &**n == name)?;
        if i < self.captured {
            self.used_capture.set(true);
        }
        Some(&self.names[i].1)
    }
}

/// A loaded and (lazily) resolved TLA+ program.
pub struct Program {
    pub files: Vec<SourceFile>,
    pub vars: Vec<VarInfo>,
    pub consts: Vec<ConstInfo>,
    pub defs: Vec<Def>,
    pub locals: Vec<LocalInfo>,
    /// The variables of instantiated modules inside `ENABLED`
    /// (`ExprKind::InstVar`), qualified by their instance.
    pub inst_vars: Vec<VarInfo>,
    /// ASSUME expressions of the root module and its EXTENDS closure.
    pub assumes: Vec<Expr>,
    pub errors: Vec<SemaError>,
    exprs: Vec<Expr>,
    root_mod: ModIdx,

    search_paths: Vec<PathBuf>,
    /// `TLX_CLASSPATH`: directories searched after the bundled standard and
    /// community modules (TLC's classpath).
    late_paths: Vec<PathBuf>,
    mods: Vec<ModInfo>,
    mod_by_name: HashMap<Arc<str>, ModIdx>,
    ctxs: Vec<Ctx>,
    scopes: Vec<Scope>,
    scope_of: HashMap<(CtxId, ModIdx), ScopeId>,
    insts: Vec<InstInfo>,
    def_src: Vec<DefSrc>,
    /// Number of leading instance params of each def.
    def_inst: Vec<usize>,
    anon_inst_ctx: HashMap<(CtxId, ModIdx, usize), CtxId>,
    /// The names a nested module sees from its parent, keyed by (the
    /// parent's context, the nested module): those bound in the parent
    /// before the nested module begins (SANY's scoping).
    nested_prefix: HashMap<(CtxId, ModIdx), HashMap<Arc<str>, Sym>>,
    /// The `InstVar` slot of each VARIABLE (by name) of a fresh context.
    inst_var_slot: HashMap<(CtxId, Arc<str>), u32>,
    /// Synthetic definitions created for subexpression references `D!sel`,
    /// keyed by the selected definition and the (normalized) selector path.
    subexpr_defs: HashMap<(DefId, Vec<SelKey>), DefId>,
    /// Entry definitions (see `entry_def`): the definition each one stands
    /// for, and the entry of each definition reached by a qualified name.
    entry_of: HashMap<DefId, DefId>,
    qualified_entry: HashMap<DefId, DefId>,
    worklist: Vec<DefId>,
    /// Stack of definitions currently being resolved (for recording instance
    /// substitution level constraints on their parameters).
    resolving_def: Vec<DefId>,
    /// Substituted declaration expressions used in each definition, paired with
    /// the maximum level allowed by the declaration (`0` for constants of
    /// non-constant modules, `1` for variables).
    def_subst_bounds: Vec<Vec<(Expr, u8)>>,
    /// Level summaries of the definitions, computed by `check_levels`.
    level_memo: Vec<Option<Arc<level::Summary>>>,
}

fn err(span: Span, msg: impl Into<String>) -> SemaError {
    SemaError { span, message: msg.into(), file: None }
}

impl Program {
    /// Load the root module from `path` (and everything it depends on).
    /// Module lookup order: see `find_module`.
    pub fn load(path: &Path, search_paths: &[PathBuf]) -> Result<Program, Vec<SemaError>> {
        Program::load_with_late(path, search_paths, &[])
    }

    /// `load`, with `late_paths` searched after the bundled standard and
    /// community modules (`TLX_CLASSPATH`; TLC's classpath).
    pub fn load_with_late(path: &Path, search_paths: &[PathBuf], late_paths: &[PathBuf]) -> Result<Program, Vec<SemaError>> {
        let mut sp = Vec::new();
        if let Some(dir) = path.parent() {
            sp.push(if dir.as_os_str().is_empty() { PathBuf::from(".") } else { dir.to_path_buf() });
        }
        sp.extend(search_paths.iter().cloned());
        let mut p = Program {
            files: Vec::new(),
            vars: Vec::new(),
            consts: Vec::new(),
            defs: Vec::new(),
            locals: Vec::new(),
            inst_vars: Vec::new(),
            assumes: Vec::new(),
            errors: Vec::new(),
            exprs: Vec::new(),
            root_mod: 0,
            search_paths: sp,
            late_paths: late_paths.to_vec(),
            mods: Vec::new(),
            mod_by_name: HashMap::new(),
            ctxs: vec![Ctx { inst_params: Vec::new(), subst: None, uses_capture: false, fresh: None, copy_of: None }],
            scopes: Vec::new(),
            scope_of: HashMap::new(),
            insts: Vec::new(),
            def_src: Vec::new(),
            def_inst: Vec::new(),
            anon_inst_ctx: HashMap::new(),
            nested_prefix: HashMap::new(),
            inst_var_slot: HashMap::new(),
            subexpr_defs: HashMap::new(),
            entry_of: HashMap::new(),
            qualified_entry: HashMap::new(),
            worklist: Vec::new(),
            resolving_def: Vec::new(),
            def_subst_bounds: Vec::new(),
            level_memo: Vec::new(),
        };
        let src = std::fs::read_to_string(path).map_err(|e| vec![err(Span::default(), format!("cannot read {}: {e}", path.display()))])?;
        let root = match p.add_module_source(path.to_path_buf(), src.into(), ModuleOrigin::User) {
            Ok(root) => root,
            Err(es) => return Err(p.annotate_files(es)),
        };
        p.root_mod = root;
        p.check_names();
        if !p.errors.is_empty() {
            return Err(p.take_load_errors());
        }
        p.scope(ROOT_CTX, root);
        p.collect_assumes(root, &mut Vec::new());
        // Like SANY, check everything (not only what the model uses).
        p.resolve_everything();
        if p.errors.is_empty() {
            p.check_levels();
        }
        if p.errors.is_empty() {
            p.check_proof_levels();
        }
        if p.errors.is_empty() {
            p.index_exprs();
            Ok(p)
        } else {
            Err(p.take_load_errors())
        }
    }

    /// The accumulated errors, without duplicates.
    fn take_load_errors(&mut self) -> Vec<SemaError> {
        let taken = std::mem::take(&mut self.errors);
        let errors = self.annotate_files(taken);
        let mut out: Vec<SemaError> = Vec::new();
        for e in errors {
            if !out.iter().any(|o| o.span == e.span && o.message == e.message) {
                out.push(e);
            }
        }
        out
    }

    /// Attach to each error the source file its span points into, so a
    /// caller that only has the errors can still name the file.
    fn annotate_files(&self, errors: Vec<SemaError>) -> Vec<SemaError> {
        errors
            .into_iter()
            .map(|mut e| {
                if e.file.is_none() {
                    if let Some(f) = self.files.get(e.span.file.0 as usize) {
                        e.file = Some(Arc::new(f.path.clone()));
                    }
                }
                e
            })
            .collect()
    }

    pub fn file(&self, id: FileId) -> &SourceFile {
        &self.files[id.0 as usize]
    }

    /// Whether `d` is a standard- or community-module definition that TLC
    /// overrides by a Java method taking eagerly evaluated arguments
    /// (`TLC_STD_STRICT` / `TLC_OVERRIDES`), matched by `(module, operator)`
    /// wherever the module was found (as in TLC; see `CG1`, `CG2`).
    ///
    /// Ordinary TLA+ definitions and `LET`-local definitions always take their
    /// arguments lazily.
    pub fn is_strict_call_def(&self, d: DefId) -> bool {
        if self.def_is_let(d) {
            return false;
        }
        let Some(def) = self.defs.get(d.idx()) else { return false };
        let Some(src) = self.def_src.get(d.idx()) else { return false };
        let module = &*self.mods[src.module].name;
        let name = def.name.rsplit('!').next().unwrap_or(&def.name);
        crate::builtins::TLC_STD_STRICT.iter().any(|(m, ops)| *m == module && ops.contains(&name))
            || crate::builtins::TLC_OVERRIDES.iter().any(|(m, ops)| *m == module && ops.contains(&name))
    }

    /// The instance context definition `d` belongs to, if it was
    /// instantiated by an INSTANCE (with substitutions): the context's id
    /// and the INSTANCE statement (TLC's substitution node, whose location
    /// TLC reports for the definition seen from outside the instance).
    pub fn def_instance(&self, d: DefId) -> Option<(usize, Span)> {
        let ctx = self.def_src.get(d.idx())?.ctx;
        let s = self.ctxs.get(ctx)?.subst.as_ref()?;
        Some((ctx, s.span))
    }

    /// The name of definition `d` as SANY names it: qualified by the named
    /// instances it was instantiated through (`I!J!Op`; an anonymous
    /// INSTANCE adds nothing).
    pub fn def_qualified_name(&self, d: DefId) -> Arc<str> {
        let name = &self.defs[d.idx()].name;
        match self.def_src.get(d.idx()).and_then(|s| self.ctx_prefix(s.ctx)) {
            Some(p) => format!("{p}!{name}").into(),
            None => name.clone(),
        }
    }

    /// The location of the name of the named INSTANCE whose context
    /// definition `d` belongs to (`I` of `I == INSTANCE M`; `I(p)` with
    /// parameters), if it is one.
    pub fn def_instance_name_span(&self, d: DefId) -> Option<Span> {
        let ctx = self.def_src.get(d.idx())?.ctx;
        let inst = self.insts.iter().find(|i| i.target.map(|t| t.0) == Some(ctx))?;
        let name = inst.ast.name.as_ref()?;
        let end = match inst.ast.params.last() {
            // (Through the closing parenthesis.)
            Some(p) => {
                let src = &self.file(name.span.file).src;
                let from = (p.name.span.end as usize).min(src.len());
                src[from..].find(')').map_or(p.name.span.end, |i| (from + i + 1) as u32)
            }
            None => name.span.end,
        };
        Some(Span { end, ..name.span })
    }

    /// The instance-name prefix of the definitions of context `ctx`.
    fn ctx_prefix(&self, ctx: CtxId) -> Option<String> {
        let ctx = self.unfresh(ctx);
        let s = self.ctxs.get(ctx)?.subst.as_ref()?;
        let outer = self.ctx_prefix(s.outer_ctx);
        let named = self.insts.iter().find(|i| i.target.map(|t| t.0) == Some(ctx)).and_then(|i| i.ast.name.as_ref());
        match (outer, named) {
            (Some(o), Some(n)) => Some(format!("{o}!{}", n.name)),
            (None, Some(n)) => Some(n.name.to_string()),
            (o, None) => o,
        }
    }

    /// The directories modules are looked up in: the root module's, then
    /// the library paths (the bundled standard modules come in between).
    pub fn search_paths(&self) -> &[PathBuf] {
        &self.search_paths
    }

    /// Look up a name in the root module's scope, resolving it (and everything
    /// it depends on) if it is a definition.
    pub fn lookup_root(&mut self, name: &str) -> Option<RootSymbol> {
        let sc = self.scope(ROOT_CTX, self.root_mod);
        let sym = *self.scopes[sc].names.get(name)?;
        match sym {
            Sym::Var(v) => Some(RootSymbol::Var(v)),
            Sym::Const(c) => Some(RootSymbol::Const(c)),
            Sym::Def(d) => {
                self.require(d);
                Some(RootSymbol::Def(d))
            }
            Sym::Decl { .. } | Sym::Instance(_) => None,
        }
    }

    /// Look up an already-resolved name in the root module's scope without
    /// mutating `self`. Returns `None` if the root scope has not been built,
    /// the name is absent, or a definition is still `Pending`.
    pub fn lookup_resolved_root(&self, name: &str) -> Option<RootSymbol> {
        let &sc = self.scope_of.get(&(ROOT_CTX, self.root_mod))?;
        let sym = *self.scopes[sc].names.get(name)?;
        match sym {
            Sym::Var(v) => Some(RootSymbol::Var(v)),
            Sym::Const(c) => Some(RootSymbol::Const(c)),
            Sym::Def(d) => (!matches!(self.defs[d.idx()].kind, DefKind::Pending)).then_some(RootSymbol::Def(d)),
            Sym::Decl { .. } | Sym::Instance(_) => None,
        }
    }

    /// TLC's check that the configuration assigns a value (or a `<-`
    /// substitution) to every constant the specification declares: the ones of
    /// the root module and of the modules it extends (SANY's
    /// `ModuleNode.getConstantDecls`); the constants of an INSTANCEd module are
    /// substituted at the INSTANCE, so they are not the configuration's
    /// business. Returns the name of the first constant the configuration does
    /// not bind, in declaration order — TLC
    /// (`SpecProcessor.processConfig`) reports one and stops
    /// (EC.TLC_CONFIG_VALUE_NOT_ASSIGNED_TO_CONSTANT_PARAM). A module-scoped
    /// form (`N = [M] v`, `N <- [M] G`) never binds a root constant.
    pub fn check_cfg_constants(&mut self, cfg: &tlx_front::cfg::Config) -> Option<String> {
        let mut bound = vec![false; self.consts.len()];
        for b in &cfg.constants {
            let (name, module) = match b {
                tlx_front::cfg::ConstBinding::Value { name, module, .. } | tlx_front::cfg::ConstBinding::Subst { name, module, .. } => {
                    (name, module)
                }
                tlx_front::cfg::ConstBinding::OpValue { name, .. } => (name, &None),
            };
            if module.is_some() {
                continue;
            }
            if let Some(RootSymbol::Const(c)) = self.lookup_root(name) {
                bound[c.idx()] = true;
            }
        }
        self.consts.iter().zip(&bound).find(|(_, b)| !**b).map(|(c, _)| c.name.to_string())
    }

    /// TLC's checks of the configuration's `<-` substitutions
    /// (`SpecProcessor.processSpec`): the left-hand side must name a root
    /// constant or operator definition (or, module-scoped, an operator
    /// definition of a module the specification uses), the right-hand side
    /// must be defined by the spec, the two must take the same number of
    /// arguments, and the right-hand side must not itself be substituted for.
    /// Returns the first error, in TLC's order (a `NoModules` only after the
    /// other module-scoped errors).
    pub fn check_cfg_substitutions(&mut self, cfg: &tlx_front::cfg::Config) -> Option<CfgSubstError> {
        use tlx_front::cfg::ConstBinding;
        // The names a plain `<-` binds: TLC's `overrides` keys.
        let plain: Vec<(String, String)> = cfg
            .constants
            .iter()
            .filter_map(|b| match b {
                ConstBinding::Subst { name, op, module: None } => Some((name.clone(), op.clone())),
                _ => None,
            })
            .collect();
        let mods: Vec<(String, String, String)> = cfg
            .constants
            .iter()
            .filter_map(|b| match b {
                ConstBinding::Subst { name, op, module: Some(m) } => Some((m.clone(), name.clone(), op.clone())),
                _ => None,
            })
            .collect();
        // The root constants the configuration assigns a value (they are in
        // TLC's `defns` and can be a right-hand side).
        let mut valued: Vec<String> = Vec::new();
        for b in &cfg.constants {
            if let ConstBinding::Value { name, module: None, .. } = b {
                if matches!(self.lookup_root(name), Some(RootSymbol::Const(_))) {
                    valued.push(name.clone());
                }
            }
        }
        // Plain substitutions: TLC walks the root constants, then the root
        // operator definitions, so a left-hand side that is neither is only
        // reported once the walk is over.
        let mut unmatched: Option<String> = None;
        for (lhs, rhs) in &plain {
            let Some(lhs_arity) = self.lhs_arity(lhs) else {
                unmatched.get_or_insert_with(|| lhs.clone());
                continue;
            };
            if plain.iter().any(|(l, _)| l == rhs) {
                return Some(CfgSubstError::RhsAppearedAfterLhs(rhs.clone()));
            }
            match self.defns_arity(rhs, &valued) {
                None => return Some(CfgSubstError::WrongSubstitution { lhs: lhs.clone(), rhs: rhs.clone() }),
                Some(rhs_arity) => {
                    if lhs_arity != rhs_arity {
                        return Some(CfgSubstError::WrongNumberOfArgs { lhs: lhs.clone(), rhs: rhs.clone() });
                    }
                }
            }
        }
        if let Some(lhs) = unmatched {
            return Some(CfgSubstError::IdDoesNotAppear(lhs));
        }
        // Module-scoped substitutions: only the operator definitions of a
        // module the specification loaded can be substituted for.
        let mut unknown: Option<String> = None;
        for (m, lhs, rhs) in &mods {
            if !self.has_module(m) {
                unknown.get_or_insert_with(|| m.clone());
                continue;
            }
            let ds = self.lookup_in_module(m, lhs);
            if ds.is_empty() {
                return Some(CfgSubstError::IdDoesNotAppear(lhs.clone()));
            }
            if mods.iter().any(|(mm, l, _)| mm == m && l == rhs) {
                return Some(CfgSubstError::RhsAppearedAfterLhs(rhs.clone()));
            }
            match self.defns_arity(rhs, &valued) {
                None => return Some(CfgSubstError::WrongSubstitution { lhs: lhs.clone(), rhs: rhs.clone() }),
                Some(rhs_arity) => {
                    if ds.iter().any(|&d| self.def_arity(d) != rhs_arity) {
                        return Some(CfgSubstError::WrongNumberOfArgs { lhs: lhs.clone(), rhs: rhs.clone() });
                    }
                }
            }
        }
        unknown.map(CfgSubstError::NoModules)
    }

    /// The arity of `name` as the left-hand side of a plain `<-`: a root
    /// constant or a root operator definition. `None`: `name` is neither.
    fn lhs_arity(&mut self, name: &str) -> Option<usize> {
        match self.lookup_root(name) {
            Some(RootSymbol::Const(c)) => Some(self.consts[c.idx()].arity),
            Some(RootSymbol::Def(d)) => Some(self.def_arity(d)),
            _ => None,
        }
    }

    /// What the right-hand side of a `<-` denotes in TLC's `defns`: an
    /// operator definition (its arity), or a 0-ary constant with a value.
    /// `None`: not defined.
    fn defns_arity(&mut self, name: &str, valued: &[String]) -> Option<usize> {
        if valued.iter().any(|v| v == name) {
            return Some(0);
        }
        match self.lookup_root(name) {
            Some(RootSymbol::Def(d)) => Some(self.def_arity(d)),
            _ => None,
        }
    }

    /// TLC's checks (`SpecProcessor.processConfig`) of the names the
    /// configuration refers to: each must be a 0-ary operator definition
    /// (a constant with a value, or a name the spec does not define, is an
    /// error). The invariants come first, then the behavior spec, then the
    /// properties, then the constraints — TLC's order.
    pub fn check_cfg_defs(&mut self, cfg: &tlx_front::cfg::Config) -> Option<CfgNameError> {
        for name in &cfg.invariants {
            if let Some(e) = self.cfg_def("invariant", name, cfg, true) {
                return Some(e);
            }
        }
        if cfg.specification.is_some() && (cfg.init.is_some() || cfg.next.is_some()) {
            return Some(CfgNameError::NotBothSpecAndInit);
        }
        if let Some(name) = &cfg.specification {
            if let Some(e) = self.cfg_def("name", name, cfg, false) {
                return Some(e);
            }
        } else {
            if let Some(name) = &cfg.init {
                if let Some(e) = self.cfg_def("initial predicate", name, cfg, false) {
                    return Some(e);
                }
            }
            if let Some(name) = &cfg.next {
                if let Some(e) = self.cfg_def("next state action", name, cfg, false) {
                    return Some(e);
                }
            }
        }
        for name in &cfg.properties {
            if let Some(e) = self.cfg_def("property", name, cfg, true) {
                return Some(e);
            }
        }
        for name in &cfg.constraints {
            if let Some(e) = self.cfg_def("constraint", name, cfg, true) {
                return Some(e);
            }
        }
        for name in &cfg.action_constraints {
            if let Some(e) = self.cfg_def("action constraint", name, cfg, true) {
                return Some(e);
            }
        }
        None
    }

    /// `name` as an INIT/NEXT/SPECIFICATION/INVARIANT/... reference.
    ///
    /// TLC looks the name up in `defns`, which maps a cfg-assigned constant
    /// to its *value* and a `<-`-substituted name to the right-hand side's
    /// binding (operator definition or valued constant). A value of `TRUE`
    /// stands in for the name in an invariant/property/constraint (when
    /// `allow_true_const` is true).
    fn cfg_def(&mut self, what: &'static str, name: &str, cfg: &tlx_front::cfg::Config, allow_true_const: bool) -> Option<CfgNameError> {
        let target = cfg.last_constant_subst(name).unwrap_or(name);
        match self.lookup_root(target) {
            Some(RootSymbol::Def(d)) if self.defs[d.idx()].params.is_empty() => None,
            Some(RootSymbol::Def(_)) => Some(CfgNameError::RequiresNoArg { what, name: name.to_string() }),
            Some(RootSymbol::Const(_))
                if allow_true_const && matches!(cfg.last_constant_value(target), Some(tlx_front::cfg::CfgValue::Bool(true))) =>
            {
                None
            }
            Some(RootSymbol::Const(_)) => Some(CfgNameError::IsConstant { what, name: name.to_string() }),
            _ => Some(CfgNameError::NotDefined { what, name: name.to_string() }),
        }
    }

    /// Resolve every definition reachable from the root module's own
    /// definitions (used to validate whole specs).
    #[doc(hidden)]
    pub fn resolve_all_root(&mut self) {
        let sc = self.scope(ROOT_CTX, self.root_mod);
        let mut ds: Vec<DefId> = self.scopes[sc].names.values().filter_map(|s| if let Sym::Def(d) = s { Some(*d) } else { None }).collect();
        ds.sort();
        for d in ds {
            self.require(d);
        }
    }

    /// Resolve every definition of every module in every context it is used
    /// in (instantiating every named instance).
    fn resolve_everything(&mut self) {
        let (mut nscopes, mut ninsts) = (0, 0);
        while nscopes < self.scopes.len() || ninsts < self.insts.len() {
            while ninsts < self.insts.len() {
                if let Some((c, m)) = self.named_instance(InstId(ninsts)) {
                    self.scope(c, m);
                }
                ninsts += 1;
            }
            while nscopes < self.scopes.len() {
                let mut ds: Vec<DefId> =
                    self.scopes[nscopes].names.values().filter_map(|s| if let Sym::Def(d) = s { Some(*d) } else { None }).collect();
                ds.sort();
                for d in ds {
                    self.require(d);
                }
                nscopes += 1;
            }
        }
    }

    /// Take accumulated errors.
    pub fn take_errors(&mut self) -> Vec<SemaError> {
        std::mem::take(&mut self.errors)
    }

    /// Whether `e` refers to a variable of an instantiated module inside
    /// `ENABLED` (`ExprKind::InstVar`), directly or through the definitions
    /// it applies (those resolved for such an `ENABLED`).
    pub fn mentions_inst_var(&self, e: &Expr) -> bool {
        let here = match &*e.kind {
            ExprKind::InstVar { .. } => true,
            ExprKind::Apply { op: OpRef::Def(d), .. } | ExprKind::OpArg(OpRef::Def(d)) => self.in_enabled_copy(*d),
            ExprKind::Let { defs, .. } => defs.iter().any(|d| self.in_enabled_copy(*d)),
            _ => false,
        };
        let mut found = here;
        if !found {
            crate::visit::children(e, &mut |c| found = found || self.mentions_inst_var(c));
        }
        found
    }

    /// Whether definition `d` was resolved for an `ENABLED` in an instance
    /// (in a context copy, see `enabled_ctx`, or an instance within one).
    fn in_enabled_copy(&self, d: DefId) -> bool {
        let Some(src) = self.def_src.get(d.idx()) else { return false };
        let mut c = src.ctx;
        loop {
            let ctx = &self.ctxs[c];
            if ctx.copy_of.is_some() {
                return true;
            }
            match &ctx.subst {
                Some(s) => c = s.outer_ctx,
                None => return false,
            }
        }
    }

    /// Whether `d` is a LET definition (its body may reference enclosing
    /// locals), or a definition of a LET INSTANCE whose substitutions do.
    pub fn def_is_let(&self, d: DefId) -> bool {
        let src = &self.def_src[d.idx()];
        if src.state == DefState::Local {
            return true;
        }
        let mut c = src.ctx;
        while let Some(s) = &self.ctxs[c].subst {
            if self.ctxs[c].uses_capture {
                return true;
            }
            c = s.outer_ctx;
        }
        false
    }

    /// Whether a module with this name was loaded.
    pub fn has_module(&self, name: &str) -> bool {
        self.mod_by_name.contains_key(name)
    }

    /// Definitions that `name` denotes in the scope of module `module`, in every
    /// context (root or instance) in which that module has been used.
    pub fn lookup_in_module(&mut self, module: &str, name: &str) -> Vec<DefId> {
        let Some(&m) = self.mod_by_name.get(module) else { return Vec::new() };
        let mut out: Vec<DefId> = self
            .scope_of
            .iter()
            .filter(|((_, mm), _)| *mm == m)
            .filter_map(|(_, &sc)| match self.scopes[sc].names.get(name) {
                Some(Sym::Def(d)) => Some(*d),
                _ => None,
            })
            .collect();
        out.sort();
        out.dedup();
        for &d in &out {
            self.require(d);
        }
        out
    }

    /// All definitions with the given (unqualified) name, resolving them.
    pub fn defs_named(&mut self, name: &str) -> Vec<DefId> {
        let ds: Vec<DefId> =
            (0..self.defs.len()).map(|i| DefId(i as u32)).filter(|d| &*self.defs[d.idx()].name == name && !self.def_is_let(*d)).collect();
        for &d in &ds {
            self.require(d);
        }
        ds
    }

    /// Definition `d` and its copies in every context its module is used in
    /// (instances, `ENABLED` copies): the definitions SANY represents by one
    /// OpDefNode, which a cfg override of `d` replaces everywhere (TLC sets
    /// the override on that node, so the bodies of every instance see it).
    /// Entry definitions are other nodes (`entry_def`): an entry `d` is only
    /// itself, and the copies of an original leave its entries out.
    pub fn def_copies(&mut self, d: DefId) -> Vec<DefId> {
        if self.def_is_let(d) || self.entry_of.contains_key(&d) {
            return vec![d];
        }
        let (module, name) = (self.def_src[d.idx()].module, self.defs[d.idx()].name.clone());
        let ds: Vec<DefId> = (0..self.defs.len())
            .map(|i| DefId(i as u32))
            .filter(|&c| {
                self.def_src[c.idx()].module == module
                    && self.defs[c.idx()].name == name
                    && !self.def_is_let(c)
                    && !self.entry_of.contains_key(&c)
            })
            .collect();
        for &c in &ds {
            self.require(c);
        }
        ds
    }

    /// The entry definitions (see `entry_def`) and the definition each one
    /// stands for, in id order.
    pub fn entry_defs(&self) -> Vec<(DefId, DefId)> {
        let mut es: Vec<(DefId, DefId)> = self.entry_of.iter().map(|(&e, &d)| (e, d)).collect();
        es.sort();
        es
    }

    /// `ds` and, transitively, the entry definitions that stand for them.
    pub fn with_entries(&mut self, mut ds: Vec<DefId>) -> Vec<DefId> {
        let mut i = 0;
        while i < ds.len() {
            let d = ds[i];
            let mut es: Vec<DefId> = self.entry_of.iter().filter(|&(_, &t)| t == d).map(|(&e, _)| e).collect();
            es.sort();
            for e in es {
                if !ds.contains(&e) {
                    self.require(e);
                    ds.push(e);
                }
            }
            i += 1;
        }
        ds
    }

    /// A definition of its own for `d` as it is entered from outside its
    /// module, by `I!Op` or imported by an anonymous INSTANCE with
    /// parameters: SANY gives such a use a new OpDefNode (with the same body,
    /// under the INSTANCE's substitutions; Generator.generateInstance and
    /// the instances of module definitions), while the bodies of the module
    /// keep referring to the original node. A cfg override binds one node,
    /// the one the root module's name denotes (SpecProcessor), so the two
    /// differ when one of them is overridden: `LET CC == INSTANCE M IN
    /// CC!Op` in the replacement of `Op` calls the original body. The
    /// interpreter makes an entry whose node is not overridden an alias of
    /// `d` (docs/compat.md D-23).
    fn entry_def(&mut self, d: DefId) -> DefId {
        if self.defs[d.idx()].builtin.is_some() || self.def_is_let(d) {
            return d;
        }
        let src = &self.def_src[d.idx()];
        let src = DefSrc { ctx: src.ctx, module: src.module, unit: src.unit.clone(), state: DefState::Unresolved };
        let e = self.new_def(self.defs[d.idx()].name.clone(), None, self.defs[d.idx()].span, src);
        self.entry_of.insert(e, d);
        e
    }

    /// `d` reached by an instance-qualified name `I!Op`: its entry
    /// definition if a cfg override of the root module could tell the two
    /// apart (the root module's name for it denotes the original), else `d`.
    fn qualified_def(&mut self, d: DefId) -> DefId {
        if let Some(&e) = self.qualified_entry.get(&d) {
            return e;
        }
        let sc = self.scope(ROOT_CTX, self.root_mod);
        let original = match self.scopes[sc].names.get(&self.defs[d.idx()].name) {
            Some(&Sym::Def(r)) => !self.entry_of.contains_key(&r) && self.def_src[r.idx()].module == self.def_src[d.idx()].module,
            _ => false,
        };
        if !original {
            return d;
        }
        let e = self.entry_def(d);
        self.qualified_entry.insert(d, e);
        e
    }

    /// Resolve a definition and everything it transitively references.
    pub fn require(&mut self, d: DefId) {
        self.worklist.push(d);
        self.drain_worklist();
    }

    // ------------------------------------------------------------------
    // definitions

    fn drain_worklist(&mut self) {
        while let Some(d) = self.worklist.pop() {
            if self.def_src[d.idx()].state == DefState::Unresolved {
                self.resolve_def(d);
            }
        }
    }

    /// Queue a module-level definition for (lazy) resolution.
    fn enqueue(&mut self, d: DefId) {
        if self.def_src[d.idx()].state == DefState::Unresolved {
            self.worklist.push(d);
        }
    }

    fn resolve_def(&mut self, d: DefId) {
        self.def_src[d.idx()].state = DefState::InProgress;
        let (ctx, module) = (self.def_src[d.idx()].ctx, self.def_src[d.idx()].module);
        let span = self.defs[d.idx()].span;
        let mut env = Env::new(ctx, module);
        let mut params = Vec::new();
        for (n, a) in self.ctxs[ctx].inst_params.clone() {
            let l = self.new_local(n, a, span);
            env.inst_args.push(self.local_ref(l, span));
            params.push(l);
        }
        let unit = self.def_src[d.idx()].unit.clone();
        let _ = self.fill_def(&mut env, d, &unit, params);
        self.def_src[d.idx()].state = DefState::Done;
    }

    /// Reference to local parameter `l` (`Local` for 0-ary, `OpArg(Param)` for
    /// higher-order operator parameters).
    pub(super) fn local_ref(&self, l: LocalId, span: Span) -> Expr {
        if self.locals[l.idx()].arity == 0 {
            Expr::new(ExprKind::Local(l), span)
        } else {
            Expr::new(ExprKind::OpArg(OpRef::Param(l)), span)
        }
    }

    /// Resolve `unit` in `env` and store the result as definition `d`.
    /// `params` are leading parameters already bound in `env` (instance params).
    fn fill_def(&mut self, env: &mut Env, d: DefId, unit: &DefUnit, mut params: Vec<LocalId>) -> Result<(), ()> {
        self.resolving_def.push(d);
        let r = self.def_body(env, unit, &mut params);
        self.resolving_def.pop();
        self.defs[d.idx()].params = params;
        self.defs[d.idx()].kind = r?;
        Ok(())
    }

    /// Resolve the parameters and body of a definition in `env`
    /// (params are appended to `params` and visible only in the body).
    fn def_body(&mut self, env: &mut Env, unit: &DefUnit, params: &mut Vec<LocalId>) -> Result<DefKind, ()> {
        self.scoped(env, |p, env| match unit {
            DefUnit::Op(od) => {
                for prm in &od.params {
                    let l = p.new_local(prm.name.name.clone(), prm.arity, prm.name.span);
                    params.push(l);
                    env.names.push((prm.name.name.clone(), LocalBinding::Local(l, prm.arity)));
                }
                p.expr(env, &od.body).map(DefKind::Op)
            }
            DefUnit::Fn(fd) => {
                let bounds = p.bounds(env, &fd.bounds)?;
                let body = p.expr(env, &fd.body)?;
                Ok(DefKind::Fn { bounds, body })
            }
        })
    }

    fn new_def(&mut self, name: Arc<str>, builtin: Option<crate::builtins::Builtin>, span: Span, src: DefSrc) -> DefId {
        let id = DefId(self.defs.len() as u32);
        let inst = if src.state == DefState::Local { 0 } else { self.ctxs[src.ctx].inst_params.len() };
        self.defs.push(Def { name, params: Vec::new(), kind: DefKind::Pending, builtin, span });
        self.def_src.push(src);
        self.def_inst.push(inst);
        self.def_subst_bounds.push(Vec::new());
        id
    }

    fn new_local(&mut self, name: Arc<str>, arity: usize, span: Span) -> LocalId {
        let id = LocalId(self.locals.len() as u32);
        self.locals.push(LocalInfo { name, arity, span });
        id
    }

    /// Declared arity (excluding instance params) of a definition.
    fn def_arity(&self, d: DefId) -> usize {
        match &self.def_src[d.idx()].unit {
            DefUnit::Op(o) => o.params.len(),
            DefUnit::Fn(_) => 0,
        }
    }

    /// Record an error and fail.
    fn fail<T>(&mut self, span: Span, msg: impl Into<String>) -> Result<T, ()> {
        self.errors.push(err(span, msg));
        Err(())
    }
}
