//! Builtin transfer rules: the shape of a builtin application and of the
//! special forms that assign a variable (`builtin_expr`).

use tlx_sema::builtins::Builtin as B;
use tlx_sema::hir::*;

use super::super::shape::{Sh, ALL};
use super::Analyzer;

impl<'a> Analyzer<'a> {
    pub(super) fn builtin_expr(&mut self, op: B, args: &[Expr], span: Span) -> Sh {
        let ip = self.ip;
        if let Some(d) = ip.builtin_override(op) {
            return self.apply(&OpRef::Def(d), args, span);
        }
        match (op, args) {
            (B::Prime, [x]) => return self.expr(x),
            (B::Eq, [a, b]) => {
                let (sa, sb) = (self.expr(a), self.expr(b));
                if let Some(v) = self.target(a) {
                    self.assign(v, &sb);
                }
                if let Some(v) = self.target(b) {
                    self.assign(v, &sa);
                }
                return Sh::plain();
            }
            (B::In, [a, s]) => {
                self.expr(a);
                let el = self.expr(s).elems();
                if let Some(v) = self.target(a) {
                    self.assign(v, &el);
                }
                return Sh::plain();
            }
            (B::SubsetEq, [a, s]) => {
                self.expr(a);
                let sub = Sh::set(self.expr(s).elems());
                if let Some(v) = self.target(a) {
                    self.assign(v, &sub);
                }
                return Sh::plain();
            }
            (B::TLCGet, [x]) if matches!(&*x.kind, ExprKind::Str(s) if &**s == "level" || &**s == "config") => {
                self.expr(x);
                if matches!(&*x.kind, ExprKind::Str(s) if &**s == "config") {
                    self.breaker(self.string_mask, "TLCGet(\"config\")", span);
                }
                return Sh::plain();
            }
            _ => {}
        }
        let shs: Vec<Sh> = args.iter().map(|a| self.expr(a)).collect();
        self.builtin(op, &shs, span)
    }

    /// The result of the builtin `op` on arguments of shapes `a`. The
    /// exhaustive match below is the dispatch: every operation family has
    /// an arm, and the rules with a body of their own are the helpers
    /// named after the family they belong to.
    pub(super) fn builtin(&mut self, op: B, a: &[Sh], span: Span) -> Sh {
        let arg = |i: usize| a.get(i).cloned().unwrap_or_default();
        let plain = Sh::plain;
        match op {
            // Predicates and numbers.
            B::Eq | B::Neq | B::In | B::NotIn | B::Not | B::Implies | B::Equiv => plain(),
            B::SubsetEq | B::IsFiniteSet | B::IsABag => plain(),
            B::Lt | B::Gt | B::Le | B::Ge => {
                self.breaker((arg(0).scalar_mask() | arg(1).scalar_mask()) & self.string_mask, op.name(), span);
                plain()
            }
            B::BagIn | B::SqSubseteq | B::IsInjective | B::GraphConnected => plain(),
            B::GraphStronglyConnected | B::UGraphConnected | B::UGraphStronglyConnected => plain(),
            B::Assert | B::AssertError | B::Unchanged | B::Enabled | B::Always => plain(),
            B::Eventually | B::LeadsTo | B::Compose | B::WhilePlus | B::Plus | B::Minus => plain(),
            B::Mul | B::Pow | B::Div | B::Mod | B::Neg | B::Cardinality => plain(),
            B::Len | B::Atoi => {
                self.breaker(arg(0).scalar_mask() & self.string_mask, op.name(), span);
                plain()
            }
            B::BagCardinality | B::CopiesIn | B::Gcd | B::Choose => plain(),
            B::Prime | B::TLCEval => arg(0),
            B::TLCCache => arg(0),
            B::Boolean | B::Nat | B::Int => Sh::set(plain()),
            B::StringSet => Sh::set(Sh::scalar(self.string_mask)),
            B::DotDot => Sh::set(plain()),
            B::Any => Sh::set(Sh::any(0)),
            // Sets.
            B::Subset => Sh::set(Sh::set(arg(0).elems())),
            B::KSubset => Sh::set(Sh::set(arg(1).elems())),
            B::Union => Sh::set(arg(0).elems().elems()),
            B::Domain => Sh::set(arg(0).dom()),
            B::Cup => Sh::set(arg(0).elems().join(&arg(1).elems())),
            B::Cap | B::SetMinus => Sh::set(arg(0).elems()),
            B::Times => Sh::set(Sh::tup(a.iter().map(|s| s.elems()).collect())),
            B::Permutations => self.permutations(arg(0)),
            B::SetToSeqs => Sh::set(Sh::seq(arg(0).elems())),
            // Sequences (and strings).
            B::Seq => Sh::set(Sh::seq(arg(0).elems())),
            B::Concat => {
                if arg(0).may_be_scalar() || arg(1).may_be_scalar() {
                    self.breaker(self.string_mask, "\\o", span);
                }
                Sh::seq(arg(0).range().join(&arg(1).range())).join(&arg(0).scalar_part()).join(&arg(1).scalar_part())
            }
            B::Append => Sh::seq(arg(0).range().join(&arg(1))),
            B::Head => arg(0).range(),
            B::Tail | B::SubSeq => {
                if arg(0).may_be_scalar() {
                    self.breaker(self.string_mask, op.name(), span);
                }
                Sh::seq(arg(0).range()).join(&arg(0).scalar_part())
            }
            // The result holds `r`'s and `t`'s elements (`s` is only searched
            // for), or is `r` or `t` itself (the definition's first two
            // guards); with three strings it is a string, like `\o`'s.
            B::ReplaceAllSubSeqs => {
                if arg(0).may_be_scalar() || arg(1).may_be_scalar() || arg(2).may_be_scalar() {
                    self.breaker(self.string_mask, op.name(), span);
                }
                Sh::seq(arg(0).range().join(&arg(2).range())).join(&arg(0)).join(&arg(2))
            }
            B::SelectSeq => self.select_seq(arg(0), arg(1), span),
            B::SortSeq => self.sort_seq(arg(0), arg(1), span),
            B::AllSubSeqs => Sh::set(Sh::seq(arg(0).range())),
            B::SelectInSubSeq | B::SelectLastInSubSeq => self.select_in_sub_seq(arg(0), arg(3), span),
            // Functions and bags.
            B::ColonGt => Sh::fcn(arg(0), arg(1)),
            B::AtAt | B::BagCup | B::BagDiff => arg(0).join(&arg(1)),
            B::EmptyBag => Sh::fcn(Sh::default(), plain()),
            B::BagUnion => arg(0).elems(),
            B::BagToSet => Sh::set(arg(0).dom()),
            B::SetToBag => Sh::fcn(arg(0).elems(), plain()),
            B::BagOfAll => self.bag_of_all(arg(0), arg(1), span),
            // Folds: the order of iteration over a set (or a function's
            // domain) follows the value order of its elements, which a
            // permutation changes, unless the operator is commutative and
            // associative.
            B::FoldSet => self.fold_set(arg(0), arg(1), arg(2), span),
            B::FoldFunction => self.fold_function(arg(0), arg(1), arg(2), span),
            B::FoldFunctionOnSet => self.fold_function_on_set(arg(0), arg(1), arg(2), arg(3), span),
            B::FoldBag => self.fold_bag(arg(0), arg(1), arg(2), span),
            B::MapThenFoldSet => self.map_then_fold_set(arg(0), arg(1), arg(2), arg(3), arg(4), span),
            // Sequence folds iterate by index on sequences; `FoldSeq` delegates
            // to `FoldFunction`, so non-sequence domains depend on key order.
            B::FoldSeq => {
                if arg(2).dom().mask() != 0 {
                    self.fold_order(&arg(0), arg(2).dom().mask(), "FoldSeq", span);
                }
                self.fold_by_index(arg(0), arg(1), arg(2), span)
            }
            B::FoldLeft | B::FoldLeftDomain => self.fold_by_index(arg(0), arg(1), arg(2), span),
            B::FoldRight | B::FoldRightDomain => self.fold_right(arg(0), arg(1), arg(2), span),
            // Graphs: structural.
            B::GraphSimplePath | B::UGraphSimplePath => Sh::set(Sh::seq(Sh::any(arg(0).mask()))),
            B::UGraphComponents => Sh::set(Sh::set(Sh::any(arg(0).mask()))),
            // Order-dependent or name-dependent operations.
            B::SetToSeq => self.set_to_seq(arg(0), span),
            B::SetMax | B::SetMin => self.set_order(op, arg(0), span),
            B::ToString | B::TLCFP | B::ToJson | B::ToJsonArray | B::ToJsonObject => self.name_writer(op, arg(0), span),
            B::CausalOrder => self.causal_order(arg(0), span),
            B::ChiSquare => self.chi_square(a, span),
            B::TLCModelValue => self.tlc_model_value(span),
            // Effects: results or side effects depend on the states
            // explored, or come from outside.
            B::Print => self.print(arg(1), span),
            B::PrintT => self.print_t(span),
            B::RandomElement => self.random_element(arg(0), span),
            B::RandomSubset => self.random_subset(arg(1), span),
            B::RandomSetOfSubsets => self.random_set_of_subsets(arg(2), span),
            B::TLCGet | B::TLCSet | B::TLCGetOrDefault | B::JavaTime | B::Trace => self.tlc_effect(op, span),
            B::IOEnv | B::IOExec | B::IOEnvExec | B::IOExecTemplate | B::IOEnvExecTemplate => self.io_effect(op, a, span),
            B::CsvWrite | B::CsvWriteRecord | B::CsvRecords | B::CsvRead => self.io_effect(op, a, span),
            B::JsonSerialize | B::JsonDeserialize | B::NdJsonSerialize | B::NdJsonDeserialize => self.io_effect(op, a, span),
            // Always an evaluation error.
            B::UnsupportedDotDiGraph | B::UnsupportedIoDeserialize | B::UnsupportedIoSerialize => Sh::default(),
            B::UnsupportedDeserialize | B::UnsupportedSerialize | B::UnsupportedSvgElemToString => Sh::default(),
            B::UnsupportedNodeOfRingNetwork | B::UnsupportedCounterExample => Sh::default(),
            B::UnsupportedToTrace | B::UnsupportedTLCEvalDefinition => Sh::default(),
        }
    }

    /// The set of all permutations of `x`'s elements.
    fn permutations(&self, x: Sh) -> Sh {
        let e = x.elems();
        Sh::set(Sh::fcn(e.clone(), e))
    }

    /// `SelectSeq`: the operator applies to every element (the order of the
    /// result is not modeled) and the result is a sequence of those elements.
    fn select_seq(&mut self, x: Sh, op: Sh, span: Span) -> Sh {
        let x = x.range();
        self.apply_ops(&op, vec![x.clone()], span);
        Sh::seq(x)
    }

    /// `SortSeq`: the comparison operator applies pairwise and the result is
    /// a sequence of the same elements.
    fn sort_seq(&mut self, x: Sh, op: Sh, span: Span) -> Sh {
        let x = x.range();
        self.apply_ops(&op, vec![x.clone(), x.clone()], span);
        Sh::seq(x)
    }

    /// `SelectInSubSeq`: the predicate applies to the sequence's elements.
    fn select_in_sub_seq(&mut self, x: Sh, op: Sh, span: Span) -> Sh {
        self.apply_ops(&op, vec![x.range()], span);
        Sh::plain()
    }

    /// `BagOfAll`: the operator applies to the bag's domain.
    fn bag_of_all(&mut self, op: Sh, bag: Sh, span: Span) -> Sh {
        let x = self.apply_ops(&op, vec![bag.dom()], span);
        Sh::fcn(x, Sh::plain())
    }

    /// `FoldSet`: fold `op` over the elements of a set.
    fn fold_set(&mut self, op: Sh, base: Sh, set: Sh, span: Span) -> Sh {
        let el = set.elems();
        self.fold_order(&op, el.mask(), "FoldSet", span);
        self.fold(&op, base, el, span)
    }

    /// `FoldFunction`: fold `op` over the range of a function's domain.
    fn fold_function(&mut self, op: Sh, base: Sh, f: Sh, span: Span) -> Sh {
        self.fold_order(&op, f.dom().mask(), "FoldFunction", span);
        self.fold(&op, base, f.range(), span)
    }

    /// `FoldFunctionOnSet`: fold `op` over a function restricted to a set.
    fn fold_function_on_set(&mut self, op: Sh, base: Sh, f: Sh, set: Sh, span: Span) -> Sh {
        self.fold_order(&op, set.elems().mask(), "FoldFunctionOnSet", span);
        self.fold(&op, base, f.range(), span)
    }

    /// `FoldBag`: fold `op` over the domain of a bag.
    fn fold_bag(&mut self, op: Sh, base: Sh, bag: Sh, span: Span) -> Sh {
        self.fold_order(&op, bag.dom().mask(), "FoldBag", span);
        self.fold(&op, base, bag.dom(), span)
    }

    /// `MapThenFoldSet`: map the set through `map`, then fold `op` over the
    /// mapped elements (`set_op` applies to the set itself).
    fn map_then_fold_set(&mut self, op: Sh, base: Sh, map: Sh, set_op: Sh, set: Sh, span: Span) -> Sh {
        let el = set.elems();
        self.fold_order(&op, el.mask(), "MapThenFoldSet", span);
        if !(self.all_commutative(&op) && self.all_chooses_first(&set_op)) {
            self.apply_ops(&set_op, vec![Sh::set(el.clone())], span);
        }
        let x = self.apply_ops(&map, vec![el], span);
        self.fold(&op, base, x, span)
    }

    /// Sequence folds iterate by index: no order of model values.
    fn fold_by_index(&mut self, op: Sh, base: Sh, seq: Sh, span: Span) -> Sh {
        let x = seq.range().join(&Sh::plain());
        self.fold(&op, base, x, span)
    }

    /// `FoldRight`/`FoldRightDomain`: fold `op` from the right over `seq`,
    /// the accumulator starting at `base`.
    fn fold_right(&mut self, op: Sh, seq: Sh, base: Sh, span: Span) -> Sh {
        let x = seq.range().join(&Sh::plain());
        self.fold(&op, base, x, span)
    }

    /// `SetToSeq`: the sequence order is the set's order.
    fn set_to_seq(&mut self, x: Sh, span: Span) -> Sh {
        let el = x.elems();
        self.breaker(el.mask(), "SetToSeq", span);
        Sh::seq(el)
    }

    /// `SetMax`/`SetMin`: the result is the extreme element by name.
    fn set_order(&mut self, op: B, x: Sh, span: Span) -> Sh {
        let el = x.elems();
        self.breaker(el.mask(), op.name(), span);
        el
    }

    /// `ToString` and the JSON/FP writer operations print the names of the
    /// values they see; `ToString` and `ToJson*` also synthesize arbitrary
    /// strings, breaking all `Str` candidates unconditionally.
    fn name_writer(&mut self, op: B, x: Sh, span: Span) -> Sh {
        let mut m = x.mask();
        if matches!(op, B::ToString | B::ToJson | B::ToJsonArray | B::ToJsonObject) {
            m |= self.string_mask;
        }
        self.breaker(m, op.name(), span);
        Sh::plain()
    }

    /// `CausalOrder`: the result depends on the order of the sequence.
    fn causal_order(&mut self, x: Sh, span: Span) -> Sh {
        self.breaker(x.mask(), "CausalOrder", span);
        x
    }

    /// `ChiSquare`: the statistic depends on the value order of every
    /// argument.
    fn chi_square(&mut self, a: &[Sh], span: Span) -> Sh {
        let m = a.iter().fold(0, |acc, s| acc | s.mask());
        self.breaker(m, "ChiSquare", span);
        Sh::plain()
    }

    /// `TLCModelValue`: a fresh model value, whose name is not fixed.
    fn tlc_model_value(&mut self, span: Span) -> Sh {
        self.breaker(ALL, "TLCModelValue", span);
        Sh::scalar(ALL)
    }

    /// `Print`: the printed value, with a side effect on the explored states.
    fn print(&mut self, value: Sh, span: Span) -> Sh {
        self.effect("Print", span);
        value
    }

    /// `PrintT`: a side effect, the result is not printed.
    fn print_t(&mut self, span: Span) -> Sh {
        self.effect("PrintT", span);
        Sh::plain()
    }

    /// `RandomElement`: a random element of the set.
    fn random_element(&mut self, x: Sh, span: Span) -> Sh {
        self.effect("RandomElement", span);
        let el = x.elems();
        self.breaker(el.mask(), "RandomElement", span);
        el
    }

    /// `RandomSubset`: a random subset of the set.
    fn random_subset(&mut self, x: Sh, span: Span) -> Sh {
        self.effect("RandomSubset", span);
        let el = x.elems();
        self.breaker(el.mask(), "RandomSubset", span);
        Sh::set(el)
    }

    /// `RandomSetOfSubsets`: a random set of subsets of the set.
    fn random_set_of_subsets(&mut self, x: Sh, span: Span) -> Sh {
        self.effect("RandomSetOfSubsets", span);
        let el = x.elems();
        self.breaker(el.mask(), "RandomSetOfSubsets", span);
        Sh::set(Sh::set(el))
    }

    /// The register/clock/statistics operations: any shape.
    fn tlc_effect(&mut self, op: B, span: Span) -> Sh {
        self.effect(op.name(), span);
        Sh::any(ALL)
    }

    /// IO and serialization: a side effect (except `IOEnv`) over an
    /// arbitrary value.
    fn io_effect(&mut self, op: B, a: &[Sh], span: Span) -> Sh {
        if op != B::IOEnv {
            self.effect(op.name(), span);
        }
        self.breaker(a.iter().fold(0, |acc, s| acc | s.mask()) | self.string_mask, op.name(), span);
        Sh::any(0)
    }
}
