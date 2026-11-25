//! Built-in operators: TLA+ core operators (always in scope) and native
//! overrides of standard-module definitions (like TLC's Java overrides).

macro_rules! builtins {
    (
        core { $($cv:ident = $cn:literal / $ca:literal [$ce:ident, $cs:ident, $cp:expr],)* }
        std { $($sv:ident = $sm:literal $sn:literal / $sa:literal [$se:ident, $ss:ident, $sp:expr],)* }
        java_only { $($jv:ident = $jm:literal $jn:literal / $ja:literal [$je:ident, $js:ident, $jp:expr],)* }
    ) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
        pub enum Builtin { $($cv,)* $($sv,)* $($jv,)* }

        impl Builtin {
            /// All registered operators, including unsupported Java overrides.
            pub const ALL: &'static [Self] = &[$(Self::$cv,)* $(Self::$sv,)* $(Self::$jv,)*];

            pub const fn metadata(self) -> Metadata {
                match self {
                    $(Self::$cv => Metadata::new($ca, Effect::$ce, Strings::$cs, $cp),)*
                    $(Self::$sv => Metadata::new($sa, Effect::$se, Strings::$ss, $sp),)*
                    $(Self::$jv => Metadata::new($ja, Effect::$je, Strings::$js, $jp),)*
                }
            }

            /// TLA+ core operator by canonical name (see `tlx_front::ast::opnames`).
            pub fn core(name: &str) -> Option<Builtin> {
                match name { $($cn => Some(Builtin::$cv),)* _ => None }
            }

            /// Native override for definition `name` of standard module `module`.
            pub fn std(module: &str, name: &str) -> Option<Builtin> {
                match (module, name) { $(($sm, $sn) => Some(Builtin::$sv),)* _ => None }
            }

            /// A definition TLC implements in Java but tlx does not support:
            /// applying it is an evaluation error, never the placeholder
            /// TLA+ definition (see docs/features.md §6.1).
            pub fn java_only(module: &str, name: &str) -> Option<Builtin> {
                match (module, name) { $(($jm, $jn) => Some(Builtin::$jv),)* _ => None }
            }

            /// The `(module, operator)` of a Java-only definition.
            pub fn java_only_name(self) -> Option<(&'static str, &'static str)> {
                match self { $(Builtin::$jv => Some(($jm, $jn)),)* _ => None }
            }

            pub fn name(self) -> &'static str {
                match self {
                    $(Builtin::$cv => $cn,)* $(Builtin::$sv => $sn,)* $(Builtin::$jv => $jn,)*
                }
            }

            /// Number of arguments; -1 for variadic.
            pub fn arity(self) -> i32 {
                self.metadata().arity
            }
        }
    };
}

builtins! {
    core {
        Eq = "=" / 2 [Pure, Never, Arguments::Values],
        Neq = "/=" / 2 [Pure, Never, Arguments::Values],
        In = "\\in" / 2 [Pure, Never, Arguments::Values],
        NotIn = "\\notin" / 2 [Pure, Never, Arguments::Values],
        Not = "~" / 1 [Pure, Never, Arguments::Special],
        Implies = "=>" / 2 [Pure, Never, Arguments::Special],
        Equiv = "<=>" / 2 [Pure, Never, Arguments::Values],
        Prime = "'" / 1 [Pure, Never, Arguments::Special],
        Unchanged = "UNCHANGED" / 1 [Pure, Never, Arguments::Special],
        Enabled = "ENABLED" / 1 [Pure, Never, Arguments::Special],
        Subset = "SUBSET" / 1 [Pure, Never, Arguments::Values],
        Union = "UNION" / 1 [Pure, Never, Arguments::Values],
        Domain = "DOMAIN" / 1 [Pure, Never, Arguments::Values],
        Cup = "\\cup" / 2 [Pure, Never, Arguments::Values],
        Cap = "\\cap" / 2 [Pure, Never, Arguments::Values],
        SetMinus = "\\" / 2 [Pure, Never, Arguments::Values],
        SubsetEq = "\\subseteq" / 2 [Pure, Never, Arguments::Values],
        Times = "\\X" / -1 [Pure, Never, Arguments::Values],
        Always = "[]" / 1 [Pure, Never, Arguments::Special],
        Eventually = "<>" / 1 [Pure, Never, Arguments::Special],
        LeadsTo = "~>" / 2 [Pure, Never, Arguments::Special],
        Compose = "\\cdot" / 2 [Pure, Never, Arguments::Special],
        WhilePlus = "-+->" / 2 [Pure, Never, Arguments::Special],
        Boolean = "BOOLEAN" / 0 [Pure, Never, Arguments::Values],
        StringSet = "STRING" / 0 [Pure, Never, Arguments::Values],
    }
    std {
        Nat = "Naturals" "Nat" / 0 [Pure, Never, Arguments::Values],
        Plus = "Naturals" "+" / 2 [Pure, Never, Arguments::Values],
        Minus = "Naturals" "-" / 2 [Pure, Never, Arguments::Values],
        Mul = "Naturals" "*" / 2 [Pure, Never, Arguments::Values],
        Pow = "Naturals" "^" / 2 [Pure, Never, Arguments::Values],
        Lt = "Naturals" "<" / 2 [Pure, Never, Arguments::Values],
        Gt = "Naturals" ">" / 2 [Pure, Never, Arguments::Values],
        Le = "Naturals" "<=" / 2 [Pure, Never, Arguments::Values],
        Ge = "Naturals" ">=" / 2 [Pure, Never, Arguments::Values],
        Div = "Naturals" "\\div" / 2 [Pure, Never, Arguments::Values],
        Mod = "Naturals" "%" / 2 [Pure, Never, Arguments::Values],
        DotDot = "Naturals" ".." / 2 [Pure, Never, Arguments::Values],
        Int = "Integers" "Int" / 0 [Pure, Never, Arguments::Values],
        Neg = "Integers" "-." / 1 [Pure, Never, Arguments::Values],
        Seq = "Sequences" "Seq" / 1 [Pure, Never, Arguments::Values],
        Len = "Sequences" "Len" / 1 [Pure, Never, Arguments::Values],
        Concat = "Sequences" "\\o" / 2 [Pure, Sequence, Arguments::Values],
        Append = "Sequences" "Append" / 2 [Pure, Never, Arguments::Values],
        Head = "Sequences" "Head" / 1 [Pure, Never, Arguments::Values],
        Tail = "Sequences" "Tail" / 1 [Pure, Sequence, Arguments::Values],
        SubSeq = "Sequences" "SubSeq" / 3 [Pure, Sequence, Arguments::Values],
        SelectSeq = "Sequences" "SelectSeq" / 2 [Pure, Never, Arguments::Operator(2)],
        IsFiniteSet = "FiniteSets" "IsFiniteSet" / 1 [Pure, Never, Arguments::Values],
        Cardinality = "FiniteSets" "Cardinality" / 1 [Pure, Never, Arguments::Values],
        Print = "TLC" "Print" / 2 [Output, Never, Arguments::Special],
        PrintT = "TLC" "PrintT" / 1 [Output, Never, Arguments::Special],
        Assert = "TLC" "Assert" / 2 [Pure, Never, Arguments::Special],
        JavaTime = "TLC" "JavaTime" / 0 [Volatile, Never, Arguments::Special],
        TLCGet = "TLC" "TLCGet" / 1 [Run, Never, Arguments::Special],
        TLCSet = "TLC" "TLCSet" / 2 [Run, Never, Arguments::Special],
        ColonGt = "TLC" ":>" / 2 [Pure, Never, Arguments::Values],
        AtAt = "TLC" "@@" / 2 [Pure, Never, Arguments::Values],
        Permutations = "TLC" "Permutations" / 1 [Pure, Never, Arguments::Values],
        SortSeq = "TLC" "SortSeq" / 2 [Pure, Never, Arguments::Operator(2)],
        RandomElement = "TLC" "RandomElement" / 1 [Volatile, Never, Arguments::Special],
        Any = "TLC" "Any" / 0 [Pure, Never, Arguments::Values],
        ToString = "TLC" "ToString" / 1 [Pure, May, Arguments::Values],
        Gcd = "DyadicRationals" "GCD" / 2 [Pure, Never, Arguments::Values],
        SetMax = "FiniteSetsExt" "Max" / 1 [Pure, Never, Arguments::Values],
        SetMin = "FiniteSetsExt" "Min" / 1 [Pure, Never, Arguments::Values],
        // FiniteSetsExt.java `kSubset`: a lazy set (TLC's KSubsetValue).
        KSubset = "FiniteSetsExt" "kSubset" / 2 [Pure, Never, Arguments::Values],
        MapThenFoldSet = "Folds" "MapThenFoldSet" / 5 [Pure, Never, Arguments::Operator(13)],
        IOEnv = "IOUtils" "IOEnv" / 0 [Pure, May, Arguments::Values],
        Atoi = "IOUtils" "atoi" / 1 [Pure, Never, Arguments::Values],
        CsvWrite = "CSV" "CSVWrite" / 3 [Volatile, Never, Arguments::Special],
        CsvRecords = "CSV" "CSVRecords" / 1 [Volatile, Never, Arguments::Special],
        IOExec = "IOUtils" "IOExec" / 1 [Volatile, May, Arguments::Special],
        IOEnvExec = "IOUtils" "IOEnvExec" / 2 [Volatile, May, Arguments::Special],
        IOExecTemplate = "IOUtils" "IOExecTemplate" / 2 [Volatile, May, Arguments::Special],
        IOEnvExecTemplate = "IOUtils" "IOEnvExecTemplate" / 3 [Volatile, May, Arguments::Special],
        CsvRead = "CSV" "CSVRead" / 3 [Volatile, May, Arguments::Special],
        CsvWriteRecord = "CSV" "CSVWriteRecord" / 4 [Volatile, Never, Arguments::Special],
        GraphConnected = "Graphs" "AreConnectedIn" / 3 [Pure, Never, Arguments::Values],
        GraphStronglyConnected = "Graphs" "IsStronglyConnected" / 1 [Pure, Never, Arguments::Values],
        UGraphConnected = "UndirectedGraphs" "AreConnectedIn" / 3 [Pure, Never, Arguments::Values],
        UGraphStronglyConnected = "UndirectedGraphs" "IsStronglyConnected" / 1 [Pure, Never, Arguments::Values],
        UGraphComponents = "UndirectedGraphs" "ConnectedComponents" / 1 [Pure, Never, Arguments::Values],
        GraphSimplePath = "Graphs" "SimplePath" / 1 [Pure, Never, Arguments::Values],
        UGraphSimplePath = "UndirectedGraphs" "SimplePath" / 1 [Pure, Never, Arguments::Values],
        TLCEval = "TLC" "TLCEval" / 1 [Pure, Never, Arguments::Values],
        // TLCExt.java `tlcGetOrDefault` (the module's definition is an
        // unbounded CHOOSE; TLCGetAndSet uses it).
        TLCGetOrDefault = "TLCExt" "TLCGetOrDefault" / 2 [Volatile, Never, Arguments::Special],
        // TLCExt.java `assertError`: whether evaluating the second argument
        // fails with exactly the message of the first (a string literal).
        AssertError = "TLCExt" "AssertError" / 2 [Pure, Never, Arguments::Special],
        // TLCExt.java `tlcModelValue`: the model value named by a string.
        TLCModelValue = "TLCExt" "TLCModelValue" / 1 [Pure, Never, Arguments::Values],
        // TLCExt.java `tlcFingerprint`: 32 bits of the value's fingerprint
        // (tlx's, not TLC's FP64: equal values have equal results).
        TLCFP = "TLCExt" "TLCFP" / 1 [Pure, Never, Arguments::Values],
        // TLCExt.java `tlcEval2`: the value of a constant-level expression
        // is kept per value of the closure.
        TLCCache = "TLCExt" "TLCCache" / 2 [Pure, Never, Arguments::Special],
        // TLCExt.java `getTrace`: the states from an initial state to the
        // current one (tlx_runtime::live::current_path).
        Trace = "TLCExt" "Trace" / 0 [Run, Never, Arguments::Special],
        RandomSubset = "Randomization" "RandomSubset" / 2 [Volatile, Never, Arguments::Special],
        RandomSetOfSubsets = "Randomization" "RandomSetOfSubsets" / 3 [Volatile, Never, Arguments::Special],
        // Bags (TLC's tlc2/module/Bags.java; SubBag has no override).
        EmptyBag = "Bags" "EmptyBag" / 0 [Pure, Never, Arguments::Values],
        IsABag = "Bags" "IsABag" / 1 [Pure, Never, Arguments::Values],
        BagCardinality = "Bags" "BagCardinality" / 1 [Pure, Never, Arguments::Values],
        BagIn = "Bags" "BagIn" / 2 [Pure, Never, Arguments::Values],
        CopiesIn = "Bags" "CopiesIn" / 2 [Pure, Never, Arguments::Values],
        BagCup = "Bags" "\\oplus" / 2 [Pure, Never, Arguments::Values],
        BagDiff = "Bags" "\\ominus" / 2 [Pure, Never, Arguments::Values],
        BagUnion = "Bags" "BagUnion" / 1 [Pure, Never, Arguments::Values],
        SqSubseteq = "Bags" "\\sqsubseteq" / 2 [Pure, Never, Arguments::Values],
        BagOfAll = "Bags" "BagOfAll" / 2 [Pure, Never, Arguments::Operator(1)],
        BagToSet = "Bags" "BagToSet" / 1 [Pure, Never, Arguments::Values],
        SetToBag = "Bags" "SetToBag" / 1 [Pure, Never, Arguments::Values],
        // BagsExt (CommunityModules' tlc2/overrides/BagsExt.java).
        FoldBag = "BagsExt" "FoldBag" / 3 [Pure, Never, Arguments::Operator(1)],
        // Folds of the community modules, overridden by Java methods that
        // iterate in TLC's normalized (sorted) order and combine
        // `acc = op(x, acc)` (`acc = op(acc, x)` for the *Left variants):
        // FiniteSetsExt.java `foldSet`, Functions.java `foldFunction` /
        // `foldFunctionOnSet` (which `FoldSeq` delegates to) and
        // SequencesExt.java `foldLeft` / `foldRight` / ...Domain.
        FoldSet = "FiniteSetsExt" "FoldSet" / 3 [Pure, Never, Arguments::Operator(1)],
        FoldFunction = "Functions" "FoldFunction" / 3 [Pure, Never, Arguments::Operator(1)],
        FoldFunctionOnSet = "Functions" "FoldFunctionOnSet" / 4 [Pure, Never, Arguments::Operator(1)],
        IsInjective = "Functions" "IsInjective" / 1 [Pure, Never, Arguments::Values],
        // VectorClocks.java: a topological sort of the log (the TLA+
        // definition is a CHOOSE over all permutations).
        CausalOrder = "VectorClocks" "CausalOrder" / 4 [Pure, Never, Arguments::Operator(14)],
        FoldSeq = "SequencesExt" "FoldSeq" / 3 [Pure, Never, Arguments::Operator(1)],
        FoldLeft = "SequencesExt" "FoldLeft" / 3 [Pure, Never, Arguments::Operator(1)],
        FoldRight = "SequencesExt" "FoldRight" / 3 [Pure, Never, Arguments::Operator(1)],
        FoldLeftDomain = "SequencesExt" "FoldLeftDomain" / 3 [Pure, Never, Arguments::Operator(1)],
        FoldRightDomain = "SequencesExt" "FoldRightDomain" / 3 [Pure, Never, Arguments::Operator(1)],
        // SequencesExt.java (Java overrides that differ from the TLA+ definition).
        AllSubSeqs = "SequencesExt" "AllSubSeqs" / 1 [Pure, Never, Arguments::Values],
        // SequencesExt.java `replaceAllSubSeq` (an `@Evaluation` override,
        // with TLC's string algorithm for three strings).
        ReplaceAllSubSeqs = "SequencesExt" "ReplaceAllSubSeqs" / 3 [Pure, Sequence, Arguments::Values],
        SelectInSubSeq = "SequencesExt" "SelectInSubSeq" / 4 [Pure, Never, Arguments::Operator(8)],
        SelectLastInSubSeq = "SequencesExt" "SelectLastInSubSeq" / 4 [Pure, Never, Arguments::Operator(8)],
        SetToSeq = "SequencesExt" "SetToSeq" / 1 [Pure, Never, Arguments::Values],
        SetToSeqs = "SequencesExt" "SetToSeqs" / 1 [Pure, Never, Arguments::Values],
        // Json (tlc2/module/Json.java; the standard module, which shadows the
        // CommunityModules copy).
        ToJson = "Json" "ToJson" / 1 [Pure, May, Arguments::Values],
        ToJsonArray = "Json" "ToJsonArray" / 1 [Pure, May, Arguments::Values],
        ToJsonObject = "Json" "ToJsonObject" / 1 [Pure, May, Arguments::Values],
        JsonSerialize = "Json" "JsonSerialize" / 2 [Volatile, Never, Arguments::Special],
        JsonDeserialize = "Json" "JsonDeserialize" / 1 [Volatile, May, Arguments::Special],
        NdJsonSerialize = "Json" "ndJsonSerialize" / 2 [Volatile, Never, Arguments::Special],
        NdJsonDeserialize = "Json" "ndJsonDeserialize" / 1 [Volatile, May, Arguments::Special],
        // Statistics.java (an Apache Commons Math Chi-square goodness of fit
        // test); the module's own definition is `TRUE`.
        ChiSquare = "Statistics" "ChiSquare" / 3 [Pure, Never, Arguments::Values],
        // Combinatorics.java `chse` (the module's `choose` definition goes
        // through `factorial`, which overflows from 13! on).
        Choose = "Combinatorics" "choose" / 2 [Pure, Never, Arguments::Values],
    }
    // Definitions whose `.tla` body is only a placeholder (`TRUE`, a constant
    // record, a bounded CHOOSE) while TLC evaluates them in Java. tlx does not
    // implement them: applying one fails instead of silently returning the
    // placeholder value (docs/features.md §6.1). Module names match both the
    // standard modules and the CommunityModules jar.
    java_only {
        UnsupportedDotDiGraph = "GraphViz" "DotDiGraph" / 3 [Pure, Never, Arguments::Special],
        UnsupportedIoDeserialize = "IOUtils" "IODeserialize" / 2 [Pure, Never, Arguments::Special],
        UnsupportedIoSerialize = "IOUtils" "IOSerialize" / 3 [Pure, Never, Arguments::Special],
        UnsupportedDeserialize = "IOUtils" "Deserialize" / 2 [Pure, Never, Arguments::Special],
        UnsupportedSerialize = "IOUtils" "Serialize" / 3 [Pure, Never, Arguments::Special],
        UnsupportedSvgElemToString = "SVG" "SVGElemToString" / 1 [Pure, Never, Arguments::Special],
        UnsupportedNodeOfRingNetwork = "SVG" "NodeOfRingNetwork" / 5 [Pure, Never, Arguments::Special],
        UnsupportedCounterExample = "TLCExt" "CounterExample" / 0 [Pure, Never, Arguments::Special],
        UnsupportedToTrace = "TLCExt" "ToTrace" / 1 [Pure, Never, Arguments::Special],
        UnsupportedTLCEvalDefinition = "TLCExt" "TLCEvalDefinition" / 1 [Pure, Never, Arguments::Special],
    }
}

/// The evaluation error for a Java-only definition TLC supports and tlx does not.
pub fn unsupported_error(module: &str, name: &str) -> String {
    format!("{module}!{name} is implemented by TLC in Java and is not supported by tlx")
}

/// Observable effects. `Run` cannot be cached during constant startup.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Effect {
    Pure,
    Output,
    Volatile,
    Run,
}

/// String creation independent of values, or only for sequence/string overloads.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Strings {
    Never,
    May,
    Sequence,
}

/// Evaluation policy; operator arguments use a zero-based argument bit mask.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Arguments {
    Values,
    Special,
    Operator(u8),
}

/// Semantic properties chosen explicitly at each builtin registration.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Metadata {
    pub arity: i32,
    pub effect: Effect,
    pub strings: Strings,
    pub arguments: Arguments,
}

impl Metadata {
    const fn new(arity: i32, effect: Effect, strings: Strings, arguments: Arguments) -> Self {
        Self { arity, effect, strings, arguments }
    }
}

impl Builtin {
    /// Replayable output (Print/PrintT), held until a compiled attempt succeeds.
    pub fn is_output(self) -> bool {
        self.metadata().effect == Effect::Output
    }
    /// Nondeterministic or effectful: never fold or memoize per state.
    pub fn is_volatile(self) -> bool {
        self.metadata().effect != Effect::Pure
    }
    /// Volatile operations TLC may evaluate once in a constant definition.
    /// TLCGet, TLCSet and Trace instead depend on the active run.
    pub fn cached_at_startup(self) -> bool {
        matches!(self.metadata().effect, Effect::Output | Effect::Volatile)
    }
    /// Syntactic string creation; eval refines sequence overloads by type.
    pub fn makes_strings(self) -> bool {
        self.metadata().strings != Strings::Never
    }
    /// A pure operation on evaluated value arguments, suitable for boxed IR.
    pub fn is_strict_value_op(self) -> bool {
        self.metadata().arguments == Arguments::Values
    }
}

#[cfg(test)]
mod metadata_tests;

/// Community modules (not shipped) whose definitions have native overrides,
/// applied by module name as TLC does.
pub const COMMUNITY_NATIVE_MODULES: &[&str] = &[
    "BagsExt",
    "CSV",
    "Combinatorics",
    "DyadicRationals",
    "FiniteSetsExt",
    "Folds",
    "Functions",
    "IOUtils",
    "Graphs",
    "SequencesExt",
    "Statistics",
    "UndirectedGraphs",
    "VectorClocks",
];

/// Definitions of community modules that TLC overrides by Java methods (the
/// `@TLAPlusOperator` annotations of `tlc2.overrides` in the CommunityModules
/// jar), by module. These evaluate their arguments eagerly (call-by-value).
pub const TLC_OVERRIDES: &[(&str, &[&str])] = &[
    ("BagsExt", &["FoldBag"]),
    ("Bitwise", &["And", "Not", "Or", "Xor", "shiftR"]),
    ("CSV", &["CSVRead", "CSVRecords", "CSVWrite", "CSVWriteRecord"]),
    ("Combinatorics", &["choose", "factorial"]),
    ("DyadicRationals", &["Reduce"]),
    ("FiniteSetsExt", &["FoldSet", "Quantify", "kSubset"]),
    ("Functions", &["AntiFunction", "FoldFunction", "FoldFunctionOnSet", "IsInjective"]),
    ("GraphViz", &["DotDiGraph"]),
    ("Graphs", &["AreConnectedIn", "IsStronglyConnected", "SimplePath"]),
    ("IOUtils", &["IODeserialize", "IOEnv", "IOEnvExec", "IOEnvExecTemplate", "IOExec", "IOExecTemplate", "IOSerialize", "atoi"]),
    ("Json", &["JsonDeserialize", "JsonSerialize", "ToJson", "ToJsonArray", "ToJsonObject", "ndJsonDeserialize", "ndJsonSerialize"]),
    ("SVG", &["NodeOfRingNetwork", "NodesOfDirectedMultiGraph", "PointOnLine", "SVGElemToString"]),
    (
        "SequencesExt",
        &[
            "AllSubSeqs",
            "Contains",
            "FoldLeft",
            "FoldLeftDomain",
            "FoldRight",
            "FoldRightDomain",
            "FoldSeq",
            "IsPrefix",
            "LongestCommonPrefix",
            "RemoveFirst",
            "RemoveFirstMatch",
            "SelectInSeq",
            "SelectInSubSeq",
            "SelectLastInSeq",
            "SelectLastInSubSeq",
            "SetToSeq",
            "SetToSeqs",
            "Suffixes",
        ],
    ),
    ("Statistics", &["ChiSquare"]),
    ("UndirectedGraphs", &["AreConnectedIn", "ConnectedComponents", "SimplePath"]),
    ("VectorClocks", &["CausalOrder"]),
];

/// Definitions of the standard modules that TLC overrides by Java methods
/// taking evaluated arguments (`@TLAPlusOperator` in `tlc2.module`) and that
/// tlx may evaluate from their TLA+ text. The remaining standard-module
/// definitions (`Bags!SubBag`, `TLCExt!AssertEq`, `TLCExt!TLCGetAndSet`,
/// `Randomization!TestRandomSetOfSubsets`, `RealTime`, LET and LAMBDA
/// operators inside them, ...) are evaluated by TLC like any TLA+ definition:
/// arguments lazily (`@Evaluation` overrides such as `TLCExt!TLCDefer` receive
/// unevaluated arguments too).
pub const TLC_STD_STRICT: &[(&str, &[&str])] = &[("TLCExt", &["TLCFP", "TLCGetOrDefault", "TLCModelValue", "TLCNoOp", "ToTrace"])];

/// Standard modules shipped with tlx (vendored sources in `modules/stdlib`,
/// owner-relative so a packaged tlx-sema always carries them, ARCH-09).
pub const STD_MODULES: &[(&str, &str)] = &[
    ("Naturals", include_str!("../modules/stdlib/Naturals.tla")),
    ("Integers", include_str!("../modules/stdlib/Integers.tla")),
    ("Reals", include_str!("../modules/stdlib/Reals.tla")),
    ("Sequences", include_str!("../modules/stdlib/Sequences.tla")),
    ("FiniteSets", include_str!("../modules/stdlib/FiniteSets.tla")),
    ("Bags", include_str!("../modules/stdlib/Bags.tla")),
    ("TLC", include_str!("../modules/stdlib/TLC.tla")),
    ("TLCExt", include_str!("../modules/stdlib/TLCExt.tla")),
    ("Randomization", include_str!("../modules/stdlib/Randomization.tla")),
    ("Json", include_str!("../modules/stdlib/Json.tla")),
    ("Toolbox", include_str!("../modules/stdlib/Toolbox.tla")),
    ("RealTime", include_str!("../modules/stdlib/RealTime.tla")),
    ("_Possible", include_str!("../modules/stdlib/_Possible.tla")),
];

/// The CommunityModules shipped with tlx (vendored sources in
/// `modules/community`, MIT license): found after the standard modules and
/// the `-I` directories, as TLC finds them on its classpath. Their Java
/// overrides are natives gated by `COMMUNITY_NATIVE_MODULES`.
pub const COMMUNITY_MODULES: &[(&str, &str)] = &[
    ("BagsExt", include_str!("../modules/community/BagsExt.tla")),
    ("Bitwise", include_str!("../modules/community/Bitwise.tla")),
    ("Combinatorics", include_str!("../modules/community/Combinatorics.tla")),
    ("CSV", include_str!("../modules/community/CSV.tla")),
    ("DifferentialEquations", include_str!("../modules/community/DifferentialEquations.tla")),
    ("DyadicRationals", include_str!("../modules/community/DyadicRationals.tla")),
    ("FiniteSetsExt", include_str!("../modules/community/FiniteSetsExt.tla")),
    ("FiniteSetsExtTheorems_proofs", include_str!("../modules/community/FiniteSetsExtTheorems_proofs.tla")),
    ("FiniteSetsExtTheorems", include_str!("../modules/community/FiniteSetsExtTheorems.tla")),
    ("Folds", include_str!("../modules/community/Folds.tla")),
    ("FoldsTheorems_proofs", include_str!("../modules/community/FoldsTheorems_proofs.tla")),
    ("FoldsTheorems", include_str!("../modules/community/FoldsTheorems.tla")),
    ("Functions", include_str!("../modules/community/Functions.tla")),
    ("FunctionTheorems_proofs", include_str!("../modules/community/FunctionTheorems_proofs.tla")),
    ("FunctionTheorems", include_str!("../modules/community/FunctionTheorems.tla")),
    ("Graphs", include_str!("../modules/community/Graphs.tla")),
    ("GraphTheorems_proofs", include_str!("../modules/community/GraphTheorems_proofs.tla")),
    ("GraphTheorems", include_str!("../modules/community/GraphTheorems.tla")),
    ("GraphViz", include_str!("../modules/community/GraphViz.tla")),
    ("HTML", include_str!("../modules/community/HTML.tla")),
    ("IOUtils", include_str!("../modules/community/IOUtils.tla")),
    ("Json", include_str!("../modules/community/Json.tla")),
    ("Quorum", include_str!("../modules/community/Quorum.tla")),
    ("QuorumTheorems_proofs", include_str!("../modules/community/QuorumTheorems_proofs.tla")),
    ("QuorumTheorems", include_str!("../modules/community/QuorumTheorems.tla")),
    ("Relation", include_str!("../modules/community/Relation.tla")),
    ("SequencesExt", include_str!("../modules/community/SequencesExt.tla")),
    ("SequencesExtTheorems_proofs", include_str!("../modules/community/SequencesExtTheorems_proofs.tla")),
    ("SequencesExtTheorems", include_str!("../modules/community/SequencesExtTheorems.tla")),
    ("ShiViz", include_str!("../modules/community/ShiViz.tla")),
    ("Statistics", include_str!("../modules/community/Statistics.tla")),
    ("SVG", include_str!("../modules/community/SVG.tla")),
    ("UndirectedGraphs", include_str!("../modules/community/UndirectedGraphs.tla")),
    ("VectorClocks", include_str!("../modules/community/VectorClocks.tla")),
];
