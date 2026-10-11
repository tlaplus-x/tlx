//! Deterministic standalone TLA+ emission from validated finite IR.

use std::fmt::Write;

use super::ir::{Domain, Model, Predicate, Update};
use super::Artifact;

pub(super) fn emit(model: &Model, remarks: &[String]) -> Artifact {
    let mut module = String::from(
        "---- MODULE Abstract ----\n\\* Generated mathematical abstraction; this file is not a safety verdict.\nEXTENDS Naturals\n",
    );
    let variables = (0..model.variables.len()).map(|i| format!("v{i}")).collect::<Vec<_>>().join(", ");
    writeln!(module, "VARIABLES {variables}").unwrap();
    let mut report = String::from(
        "Finite abstraction generated; model checking has NOT been performed.\n\
         Scope: configured scalar natural counters and named state invariants.\n\
         Semantics: mathematical naturals, not concrete backend overflow behavior.\n\
         Trust: HIR frontend, restricted lowering, Rust rule checker and TLA+ emitter.\n\
         No Lean/kernel certificate, cached proof authorization, or configuration-family claim.\n\
         Generated traces contain abstract representatives, not concrete counter values.\n\
         Re-run abstraction after any source, configuration, property or tool change.\n",
    );
    for remark in remarks {
        writeln!(report, "Pass: {remark}").unwrap();
    }
    for (i, variable) in model.variables.iter().enumerate() {
        if let Domain::Constant(value) = variable.domain {
            writeln!(
                report,
                "v{i}: {} at file {}:{}:{}; constant {value}; alpha(n) = n (exact on reachable states)",
                variable.name, variable.span.file.0, variable.span.line, variable.span.col
            )
            .unwrap();
            continue;
        }
        let Domain::Interval(cap) = variable.domain else { unreachable!("finite IR checked before emission") };
        writeln!(
            report,
            "v{i}: {} at file {}:{}:{}; domain 0..{cap}; alpha(n) = min(n, {cap}); {cap} represents all n >= {cap}",
            variable.name, variable.span.file.0, variable.span.line, variable.span.col,
        )
        .unwrap();
    }
    module.push_str("Init ==\n");
    for (i, value) in model.initial.iter().enumerate() {
        writeln!(module, "    /\\ v{i} = {value}").unwrap();
    }
    for (a, action) in model.actions.iter().enumerate() {
        writeln!(module, "Action{a} ==\n    /\\ {}", predicate(&action.guard)).unwrap();
        for (i, update) in action.updates.iter().enumerate() {
            let rhs = match update {
                Update::Keep => format!("v{i}"),
                Update::Reset => "0".to_string(),
                Update::SaturatingIncrement(cap) => format!("IF v{i} < {cap} THEN v{i} + 1 ELSE {cap}"),
                Update::Increment => unreachable!("finite IR checked before emission"),
            };
            writeln!(module, "    /\\ v{i}' = ({rhs})").unwrap();
        }
        writeln!(report, "Action{a}: file {}:{}:{}", action.span.file.0, action.span.line, action.span.col).unwrap();
    }
    let next = if model.actions.is_empty() {
        // TLC requires NEXT to be nonconstant. The false state guard makes
        // this relation empty; UNCHANGED retains action level without ever
        // admitting a self-loop.
        format!("(v0 /= v0) /\\ UNCHANGED <<{variables}>>")
    } else {
        (0..model.actions.len()).map(|i| format!("Action{i}")).collect::<Vec<_>>().join(" \\/ ")
    };
    writeln!(module, "Next == {next}").unwrap();
    let mut config = String::from("INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n");
    for (i, property) in model.properties.iter().enumerate() {
        // TLC rejects a constant FALSE invariant during configuration. Keep
        // the equivalent false predicate at state level so the initial-state
        // violation remains checkable (validated IR always has a variable).
        let text = if property.predicate == Predicate::Bool(false) { "(v0 /= v0)".to_string() } else { predicate(&property.predicate) };
        writeln!(module, "Invariant{i} == {text}").unwrap();
        writeln!(config, "INVARIANT Invariant{i}").unwrap();
        writeln!(report, "Invariant{i}: {} at file {}:{}:{}", property.name, property.span.file.0, property.span.line, property.span.col)
            .unwrap();
    }
    module.push_str("====\n");
    Artifact { module, config, report }
}

fn predicate(p: &Predicate) -> String {
    match p {
        Predicate::Bool(b) => if *b { "TRUE" } else { "FALSE" }.to_string(),
        Predicate::Compare { var, op, value } => format!("(v{var} {} {value})", op.text()),
        Predicate::Not(p) => format!("~({})", predicate(p)),
        Predicate::And(ps) | Predicate::Or(ps) => {
            let and = matches!(p, Predicate::And(_));
            if ps.is_empty() {
                return if and { "TRUE" } else { "FALSE" }.to_string();
            }
            format!("({})", ps.iter().map(predicate).collect::<Vec<_>>().join(if and { " /\\ " } else { " \\/ " }))
        }
    }
}
