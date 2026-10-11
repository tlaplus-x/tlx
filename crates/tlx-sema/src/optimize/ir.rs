//! A closed, typed transition-system IR. All values are mathematical naturals;
//! predicates cannot hide calls, effects, aliases or exact-value escapes.

use crate::hir::Span;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum Domain {
    Natural,
    /// A proved inductive singleton, retaining the original exact value.
    Constant(u32),
    /// Saturation quotient: the upper endpoint represents the entire tail.
    Interval(u32),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Variable {
    pub name: String,
    pub span: Span,
    pub domain: Domain,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Comparison {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

impl Comparison {
    pub fn reverse(self) -> Self {
        match self {
            Self::Eq | Self::Ne => self,
            Self::Lt => Self::Gt,
            Self::Le => Self::Ge,
            Self::Gt => Self::Lt,
            Self::Ge => Self::Le,
        }
    }

    pub fn test(self, a: u64, b: u64) -> bool {
        match self {
            Self::Eq => a == b,
            Self::Ne => a != b,
            Self::Lt => a < b,
            Self::Le => a <= b,
            Self::Gt => a > b,
            Self::Ge => a >= b,
        }
    }

    pub fn text(self) -> &'static str {
        match self {
            Self::Eq => "=",
            Self::Ne => "/=",
            Self::Lt => "<",
            Self::Le => "<=",
            Self::Gt => ">",
            Self::Ge => ">=",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum Predicate {
    Bool(bool),
    Compare { var: usize, op: Comparison, value: u32 },
    Not(Box<Predicate>),
    And(Vec<Predicate>),
    Or(Vec<Predicate>),
}

impl Predicate {
    pub fn observations(&self, f: &mut impl FnMut(usize, Comparison, u32)) {
        match self {
            Self::Bool(_) => {}
            Self::Compare { var, op, value } => f(*var, *op, *value),
            Self::Not(p) => p.observations(f),
            Self::And(ps) | Self::Or(ps) => ps.iter().for_each(|p| p.observations(f)),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Update {
    Keep,
    Reset,
    Increment,
    SaturatingIncrement(u32),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Action {
    pub span: Span,
    pub guard: Predicate,
    /// Exactly one update per state variable, in variable order.
    pub updates: Vec<Update>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Property {
    pub name: String,
    pub span: Span,
    pub predicate: Predicate,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Model {
    pub variables: Vec<Variable>,
    pub initial: Vec<u32>,
    pub actions: Vec<Action>,
    pub properties: Vec<Property>,
}

impl Model {
    pub fn observations(&self, f: &mut impl FnMut(usize, Comparison, u32)) {
        for action in &self.actions {
            action.guard.observations(f);
        }
        for property in &self.properties {
            property.predicate.observations(f);
        }
    }
}
