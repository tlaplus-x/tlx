//! Resolved HIR: every name is resolved to a variable, constant, definition,
//! local binding or builtin. Modules, EXTENDS and INSTANCE are gone: instantiated
//! definitions are separate `Def`s whose bodies have the substitutions applied
//! (design.md §3.2).

use std::sync::Arc;

pub use tlx_front::ast::{FairnessKind, QuantKind, Span};

use crate::builtins::Builtin;

macro_rules! id_type {
    ($name:ident) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
        pub struct $name(pub u32);
        impl $name {
            pub fn idx(self) -> usize {
                self.0 as usize
            }
        }
    };
}
id_type!(VarId);
id_type!(ConstId);
id_type!(DefId);
// A bound name: quantifier / CHOOSE / set-former / function-constructor variable,
// or an operator parameter. Unique per binding site across the whole program.
id_type!(LocalId);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExprId(pub(crate) std::num::NonZeroU32);

impl ExprId {
    pub(crate) fn idx(self) -> usize {
        self.0.get() as usize - 1
    }

    /// Dense index in `0..Program::arena_len()` (for side tables).
    pub fn index(self) -> usize {
        self.idx()
    }
}

#[derive(Clone, Debug)]
pub struct VarInfo {
    pub name: Arc<str>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct ConstInfo {
    pub name: Arc<str>,
    pub arity: usize,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct LocalInfo {
    pub name: Arc<str>,
    /// > 0 for higher-order operator parameters `F(_, _)`.
    pub arity: usize,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct Def {
    /// Display name, qualified by instance path (e.g. `I!Op`).
    pub name: Arc<str>,
    /// Leading params include the parameters of enclosing parameterized instances.
    pub params: Vec<LocalId>,
    pub kind: DefKind,
    /// Native implementation overriding the TLA+ definition (standard modules).
    pub builtin: Option<Builtin>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum DefKind {
    /// Body not resolved yet (lazy resolution) or failed to resolve.
    Pending,
    /// `Op(params) == body`
    Op(Expr),
    /// `f[x \in S] == body`: a (possibly recursive) function definition.
    /// Equivalent to `f == [x \in S |-> body]` where body may reference `f`.
    Fn { bounds: Vec<Bound>, body: Expr },
}

/// Cheap to clone (shared); use `Arc::make_mut` on `kind` to rewrite.
#[derive(Clone, Debug)]
pub struct Expr {
    pub kind: Arc<ExprKind>,
    pub span: Span,
    pub(crate) arena_id: Option<ExprId>,
}

impl Expr {
    pub fn new(kind: ExprKind, span: Span) -> Expr {
        Expr { kind: Arc::new(kind), span, arena_id: None }
    }
}

#[derive(Clone, Debug)]
pub enum BoundVars {
    Many(Vec<LocalId>),
    Tuple(Vec<LocalId>),
}

impl BoundVars {
    pub fn locals(&self) -> &[LocalId] {
        match self {
            BoundVars::Many(v) | BoundVars::Tuple(v) => v,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Bound {
    pub vars: BoundVars,
    pub set: Expr,
}

/// The callee of an operator application.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OpRef {
    Def(DefId),
    /// Operator constant `CONSTANT F(_)`.
    Const(ConstId),
    /// Higher-order operator parameter `F(_)` of the enclosing definition.
    Param(LocalId),
    Builtin(Builtin),
}

#[derive(Clone, Debug)]
pub enum ExceptKey {
    Field(Arc<str>),
    Index(Vec<Expr>),
}

#[derive(Clone, Debug)]
pub enum ExprKind {
    Num(i128),
    Decimal(Arc<str>),
    Str(Arc<str>),
    Bool(bool),
    /// A `.cfg` constant value spliced into the HIR by a certified
    /// normalization: a zero-arity definition the configuration assigns a
    /// literal (`Def = value`, docs/compat.md D-23). Resolution never produces
    /// it, so the runtime and compiled tiers never evaluate it; the certificate
    /// emitters interpret it as the configured value.
    CfgLiteral(Arc<tlx_front::cfg::CfgValue>),

    Var(VarId),
    /// A VARIABLE of an instantiated module, referenced inside an `ENABLED`
    /// of that module (`Program::inst_vars[slot]`). Unprimed it is its
    /// substitution `subst`; primed it is a variable of its own that the
    /// `ENABLED` quantifies over (SANY/TLC semantics: the substitution is not
    /// applied to the primed variables of `ENABLED A` within the instance,
    /// so `I!(ENABLED (u' = 1))` holds even where `u <- x + y` cannot reach
    /// 1 in one step; TLC's `Context.lookup` with `cutoff` at the ENABLED
    /// branch). Evaluated outside an ENABLED that provides it, it is
    /// `subst` (also primed).
    InstVar {
        slot: u32,
        subst: Expr,
    },
    /// 0-ary constant.
    Const(ConstId),
    /// Bound variable or 0-ary operator parameter.
    Local(LocalId),
    /// Application of a user definition, operator constant or higher-order param.
    /// Zero-argument definitions are `Apply` with empty args.
    Apply {
        op: OpRef,
        args: Vec<Expr>,
    },
    /// Application of a built-in operator (core TLA+ or native standard-module op).
    Builtin {
        op: Builtin,
        args: Vec<Expr>,
    },
    /// An operator passed as an argument to a higher-order operator.
    OpArg(OpRef),
    Lambda {
        params: Vec<LocalId>,
        body: Expr,
    },

    And(Vec<Expr>),
    Or(Vec<Expr>),
    Quant {
        kind: QuantKind,
        bounds: Vec<Bound>,
        body: Expr,
    },
    QuantUnbounded {
        kind: QuantKind,
        vars: Vec<LocalId>,
        body: Expr,
    },
    TemporalQuant {
        kind: QuantKind,
        vars: Vec<LocalId>,
        body: Expr,
    },
    Choose {
        vars: BoundVars,
        set: Option<Expr>,
        body: Expr,
    },

    If {
        cond: Expr,
        then: Expr,
        els: Expr,
    },
    Case {
        arms: Vec<(Expr, Expr)>,
        other: Option<Expr>,
    },
    /// LET definitions are ordinary `Def`s (they may reference enclosing locals).
    Let {
        defs: Vec<DefId>,
        body: Expr,
    },

    SetEnum(Vec<Expr>),
    SetFilter {
        bound: Bound,
        pred: Expr,
    },
    SetMap {
        expr: Expr,
        bounds: Vec<Bound>,
    },

    Tuple(Vec<Expr>),
    FnConstruct {
        bounds: Vec<Bound>,
        body: Expr,
    },
    FnApp {
        func: Expr,
        args: Vec<Expr>,
    },
    FnSet {
        domain: Expr,
        range: Expr,
    },
    Record(Vec<(Arc<str>, Expr)>),
    RecordSet(Vec<(Arc<str>, Expr)>),
    Field {
        record: Expr,
        field: Arc<str>,
    },
    Except {
        base: Expr,
        updates: Vec<(Vec<ExceptKey>, Expr)>,
    },
    At,

    BoxAction {
        action: Expr,
        sub: Expr,
    },
    AngleAction {
        action: Expr,
        sub: Expr,
    },
    Fairness {
        kind: FairnessKind,
        sub: Expr,
        action: Expr,
        /// In an instance whose substitutions are not a renaming of
        /// variables: `<<action>>_sub` resolved as the argument of the
        /// `ENABLED` that WF/SF stand for (`ExprKind::InstVar`), which
        /// fairness takes from it rather than from `action` and `sub`.
        enabled: Option<Expr>,
    },
}

/// What a name in the root module's scope refers to (for `.cfg` lookups).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RootSymbol {
    Var(VarId),
    Const(ConstId),
    Def(DefId),
}
