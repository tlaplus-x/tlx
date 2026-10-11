//! Automatic symmetry (`tlx_eval::model::autosym`): the suggestion line, the
//! application of a proven group to the search with its cross-check, and
//! the labelling of a reduced run (start line, statistics suffix, `-stats`).

use std::process::ExitCode;
use std::time::{Duration, Instant};

use tlx_base::format::{self, JsonNewline};
use tlx_eval::model::autosym::{self, Analysis};
use tlx_eval::model::symcheck::{self, Bounds};
use tlx_eval::model::InterpModel;

use crate::args::Args;
use crate::out::{self, code};
use crate::stats;

/// The automatic symmetry of this run (docs/usage.md sections 6.2 and 6.3):
/// analyze the sets of model values; under `-tlc` print the suggestion; in
/// the default mode apply the proven group when that is allowed and name
/// the optimizations of the run. The symmetry applied, if any; an internal
/// error (exit 101) if the cross-check of the proof finds a witness.
pub fn run(model: &mut InterpModel, a: &Args, guards_allowed: bool) -> Result<Option<Applied>, ExitCode> {
    if a.checksymmetry {
        return Ok(None);
    }
    if a.simulate.is_some() || !model.has_behavior {
        if !a.tlc {
            label(None);
        }
        return Ok(None);
    }
    // Exact IR optimization only accepts scalar naturals and rejects SYMMETRY,
    // so there are no model-value permutations to analyze on this path.
    if !a.optimization_rules.is_empty() {
        out::info(code::OPTIMIZATIONS_USED, &format!("Optimizations: exact IR cleanup.\n{}", a.optimization_rules.join("\n")));
        out::set_reduced("optimization");
        tlx_runtime::stats::set_json(
            "optimizations",
            r#"[{"name":"exact-ir","scope":"safety","proof":"static","preserved":["V-safe","CEX"]}]"#.into(),
        );
        return Ok(None);
    }
    let mut an = autosym::analyze(model);
    // Already-proven models retain their original analysis and execution
    // path. Only a CHOOSE rejection calls for conditional obligations.
    if tlx_base::knobs::Env::process().string_or_default("TLX_AUTOSYM_FORCE").trim().is_empty()
        && guards_allowed
        && !a.tlc
        && a.recover.is_none()
        && a.checkpoint.is_none_or(|n| n == 0)
        && an.sets.iter().any(|s| matches!(&s.verdict, autosym::Verdict::Rejected { what, .. } if what == "CHOOSE"))
    {
        an = autosym::analyze_guarded(model);
    }
    stats::phase("auto symmetry analysis", an.elapsed);
    report(&an);
    if a.tlc {
        let advice = if model.live.is_empty() { Some(not_applicable(model, &an).is_none()) } else { None };
        if let Some(line) = an.suggestion(advice) {
            out::info(code::GENERAL, &line);
        }
        return Ok(None);
    }
    let applied = apply(model, &mut an, a.noautosymmetry)?;
    label(applied.as_ref());
    Ok(applied)
}

/// Record every candidate with its result for `-stats`.
fn report(an: &Analysis) {
    let mut text = String::new();
    for s in an.proven() {
        let proof = if an.guards.is_empty() { "proven" } else { "conditional, runtime guard" };
        text.push_str(&format!("{}: {proof} {}\n", s.candidate.name, s.group_text().unwrap_or_default()));
    }
    for line in an.rejections() {
        text.push_str(&line);
        text.push('\n');
    }
    for e in &an.effects {
        text.push_str(&format!("not applicable: {e}\n"));
    }
    if !text.is_empty() {
        tlx_runtime::stats::set_section("auto symmetry", text);
    }
}

/// The largest group applied: the search tries every element of the group
/// on each state it finds.
const MAX_ORDER: u128 = 720;

/// The time the bounded cross-check of an applied group may take.
const CROSS_CHECK_TIME: Duration = Duration::from_millis(20);

/// Apply the proven symmetry of `an` to `model` when it is allowed: the
/// safety search only (no temporal properties), no declared SYMMETRY, no
/// VIEW, and no builtin whose output or result depends on the states
/// explored. Before it is applied, a bounded check of the group runs as a
/// cross-check of the proof; a witness is an internal error (exit 101).
fn apply(model: &mut InterpModel, an: &mut Analysis, off: bool) -> Result<Option<Applied>, ExitCode> {
    let forced = tlx_base::knobs::Env::process().string_or_default("TLX_AUTOSYM_FORCE");
    let forced: Vec<&str> = forced.split(',').map(str::trim).filter(|n| !n.is_empty()).collect();
    if off {
        note("not applied: -noautosymmetry");
        return Ok(None);
    }
    an.force(&forced);
    if let Some(why) = not_applicable(model, an) {
        note(&format!("not applied: {why}"));
        return Ok(None);
    }
    let (chosen, skipped) = an.select(MAX_ORDER);
    for s in &skipped {
        note(&format!("{}: not applied (the group would have more than {MAX_ORDER} elements)", s.candidate.name));
    }
    if chosen.is_empty() {
        return Ok(None);
    }
    let guarded = !an.guards.is_empty();
    let gens: Vec<_> = chosen.iter().flat_map(|s| s.generators()).collect();
    let text = chosen.iter().filter_map(|s| s.group_text()).collect::<Vec<_>>().join(" x ");
    if guarded {
        model.ip.install_symmetry_guards(an.guards.clone());
    }
    let bounds = Bounds { time: Some(CROSS_CHECK_TIME), ..Bounds::default() };
    let t0 = Instant::now();
    let check = symcheck::check_perms(model, gens.clone(), &bounds);
    stats::phase("auto symmetry cross-check", t0.elapsed());
    if let Ok(r) = &check {
        if let Some(w) = &r.witness {
            if guarded {
                note("not applied: conditional symmetry failed its bounded check");
                return Ok(None);
            }
            out::error(
                code::GENERAL,
                &format!(
                    "Internal error: the symmetry {text} that tlx proved does not hold ({}; permutation {}). Run with -noautosymmetry.",
                    w.part, w.permutation
                ),
            );
            return Err(ExitCode::from(101));
        }
    }
    if guarded {
        note("runtime guards: automatic checkpoints disabled; explicit checkpoint/recovery requests use static proofs only");
    }
    model.apply_symmetry(gens);
    Ok(Some(Applied { group: text, forced: !an.forced.is_empty(), guarded }))
}

/// A symmetry applied to the search.
pub struct Applied {
    /// The group, as TLA+ text (`Permutations(RM) x Permutations(Acceptor)`).
    pub group: String,
    /// Forced by `TLX_AUTOSYM_FORCE` (not proven).
    pub forced: bool,
    pub guarded: bool,
}

/// Name the optimizations of a run in the default mode (docs/usage.md
/// section 6.3): the start line, the suffix of the final statistics line,
/// the dump's note and the `optimizations` field of `-stats json`.
fn label(applied: Option<&Applied>) {
    let Some(a) = applied else {
        out::info(code::OPTIMIZATIONS_USED, "Optimizations: none applicable.");
        tlx_runtime::stats::set_json("optimizations", "[]".into());
        return;
    };
    let proof = if a.forced {
        "forced by TLX_AUTOSYM_FORCE, not proven"
    } else if a.guarded {
        "runtime guard"
    } else {
        "proven"
    };
    out::info(
        code::OPTIMIZATIONS_USED,
        &format!(
            "Optimizations: symmetry {} ({proof}; safety checks only).\nCounts refer to the reduced search; run with -tlc for TLC-identical statistics.",
            a.group
        ),
    );
    out::set_reduced("symmetry");
    let json =
        format!(
        "[{{\"name\":\"symmetry\",\"scope\":\"safety\",\"proof\":\"{}\",\"preserved\":[\"V-safe\",\"CEX\",\"D\",\"L\"],\"detail\":{}}}]",
        if a.forced { "none" } else if a.guarded { "runtime guard" } else { "static" },
        json_string(&a.group)
    );
    tlx_runtime::stats::set_json("optimizations", json);
}

/// `s` as a JSON string; a line feed keeps its `\u000a` spelling.
fn json_string(s: &str) -> String {
    format::json_string(s, JsonNewline::Unicode)
}

/// Why no symmetry is applied to `model` at all, if so.
fn not_applicable(model: &InterpModel, an: &Analysis) -> Option<String> {
    if !model.symmetry_maps().is_empty() || model.ip.cfg.symmetry.is_some() {
        return Some("the cfg declares a SYMMETRY".into());
    }
    if model.has_view() {
        return Some("the cfg has a VIEW".into());
    }
    if !model.live.is_empty() {
        return Some("temporal properties are checked (the proof covers safety only)".into());
    }
    if let Some(e) = an.effects.first() {
        return Some(format!("the output or results depend on the states explored ({e})"));
    }
    if an.incomplete {
        return Some("the analysis is incomplete".into());
    }
    None
}

/// A line of the `-stats` section.
fn note(line: &str) {
    let mut text = tlx_runtime::stats::section("auto symmetry").unwrap_or_default();
    text.push_str(line);
    text.push('\n');
    tlx_runtime::stats::set_section("auto symmetry", text);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn json_string_keeps_the_unicode_newline_spelling() {
        assert_eq!(json_string("{p1, p2}\n\"q\"\\\t"), "\"{p1, p2}\\u000a\\\"q\\\"\\\\\\u0009\"");
    }
}
