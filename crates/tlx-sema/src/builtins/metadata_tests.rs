//! Frozen pre-metadata classifications: exhaustively compare every registration.
use super::*;
use Builtin as B;
#[derive(Clone, Copy)]
struct Legacy(Builtin);
impl Legacy {
    /// Output only (Print, PrintT): a side effect that can be held back
    /// and replayed (the compiled tier holds it until a run succeeds).
    pub fn is_output(self) -> bool {
        matches!(self.0, Builtin::Print | Builtin::PrintT)
    }

    /// Nondeterministic or side-effecting: never evaluated at compile time,
    /// memoized per state, or treated as a pure function of its arguments.
    pub fn is_volatile(self) -> bool {
        use Builtin as B;
        matches!(
            self.0,
            B::RandomElement
                | B::RandomSubset
                | B::RandomSetOfSubsets
                | B::TLCGet
                | B::TLCSet
                | B::TLCGetOrDefault
                | B::JavaTime
                | B::Print
                | B::PrintT
                | B::IOExec
                | B::IOEnvExec
                | B::IOExecTemplate
                | B::IOEnvExecTemplate
                | B::CsvWrite
                | B::CsvWriteRecord
                | B::CsvRecords
                | B::CsvRead
                | B::JsonSerialize
                | B::JsonDeserialize
                | B::NdJsonSerialize
                | B::NdJsonDeserialize
                | B::Trace
        )
    }

    /// Volatile, yet TLC evaluates a 0-ary constant-level definition using
    /// it once, at startup (SpecProcessor.processConstantDefns caches the
    /// value). Not TLCGet/TLCSet: their startup evaluation fails or depends
    /// on the run (TLC then re-evaluates the definition at each use), and
    /// tlx keeps them uncached.
    pub fn cached_at_startup(self) -> bool {
        self.is_volatile() && !matches!(self.0, Builtin::TLCGet | Builtin::TLCSet | Builtin::Trace)
    }
}

pub fn makes_strings(op: B) -> bool {
    matches!(
        op,
        B::ToString
            | B::Concat
            | B::Tail
            | B::SubSeq
            | B::ReplaceAllSubSeqs
            | B::ToJson
            | B::ToJsonArray
            | B::ToJsonObject
            | B::IOEnv
            | B::IOExec
            | B::IOEnvExec
            | B::IOExecTemplate
            | B::IOEnvExecTemplate
            | B::CsvRead
            | B::JsonDeserialize
            | B::NdJsonDeserialize
    )
}
fn is_strict_value_op(op: B) -> bool {
    // Definitions TLC implements in Java and tlx does not support raise an
    // evaluation error: evaluate them with the interpreter (which reports it).
    if op.java_only_name().is_some() {
        return false;
    }
    // Nondeterministic or side-effecting: an interpreter node, so that the
    // function runs in the interpreter only (the IR executor would run the
    // effect again when it falls back).
    if Legacy(op).is_volatile() {
        return false;
    }
    !matches!(
        op,
        B::Prime
            | B::Unchanged
            | B::Enabled
            | B::Not
            | B::Implies
            | B::SelectSeq
            | B::SelectInSubSeq
            | B::SelectLastInSubSeq
            | B::CausalOrder
            | B::SortSeq
            | B::MapThenFoldSet
            | B::BagOfAll
            | B::FoldBag
            // Take an operator argument: evaluated by the interpreter.
            | B::FoldSet
            | B::FoldFunction
            | B::FoldFunctionOnSet
            | B::FoldSeq
            | B::FoldLeft
            | B::FoldRight
            | B::FoldLeftDomain
            | B::FoldRightDomain
            | B::TLCGet
            | B::TLCSet
            | B::AssertError
            | B::TLCCache
            | B::Always
            | B::Eventually
            | B::LeadsTo
            | B::WhilePlus
            | B::Compose
            | B::Print
            | B::PrintT
            | B::Assert
            | B::JavaTime
            | B::RandomElement
    )
}
#[test]
fn all_builtin_properties_match_legacy_consumers() {
    assert!(!Builtin::ALL.is_empty());
    for &b in Builtin::ALL {
        let old = Legacy(b);
        assert_eq!(b.is_output(), old.is_output(), "{b:?} output");
        assert_eq!(b.is_volatile(), old.is_volatile(), "{b:?} volatile");
        assert_eq!(b.cached_at_startup(), old.cached_at_startup(), "{b:?} startup");
        assert_eq!(b.makes_strings(), makes_strings(b), "{b:?} strings");
        assert_eq!(b.is_strict_value_op(), is_strict_value_op(b), "{b:?} strict");
        if let Arguments::Operator(mask) = b.metadata().arguments {
            assert!(mask > 0 && (mask as u32) < (1 << b.arity()), "{b:?} operator arguments");
        }
    }
}

#[test]
fn operator_argument_metadata_matches_bundled_signatures() {
    use std::collections::HashSet;
    let mut checked = HashSet::new();
    for &(module, _) in STD_MODULES.iter().chain(COMMUNITY_MODULES.iter().filter(|(name, _)| COMMUNITY_NATIVE_MODULES.contains(name))) {
        let dir = tlx_testkit::TempDir::new("builtin-signatures");
        let root = dir.write_modules(&[("Probe", &format!("---- MODULE Probe ----\nEXTENDS {module}\n====\n"))]);
        let p = crate::Program::load(&root, &[]).unwrap_or_else(|errors| panic!("{module}: {errors:?}"));
        for def in &p.defs {
            let Some(b) = def.builtin else { continue };
            if b.java_only_name().is_some() {
                continue;
            }
            let actual =
                def.params.iter().enumerate().fold(0, |mask, (i, p_id)| mask | if p.locals[p_id.idx()].arity > 0 { 1 << i } else { 0 });
            let declared = match b.metadata().arguments {
                Arguments::Operator(mask) => mask,
                _ => 0,
            };
            assert_eq!(actual, declared, "{module}!{}", def.name);
            checked.insert(b);
        }
    }
    for &b in Builtin::ALL {
        if Builtin::core(b.name()) != Some(b) && b.java_only_name().is_none() {
            assert!(checked.contains(&b), "missing bundled signature: {b:?}");
        }
    }
}
