//! Automatic symmetry (`tlx_eval::model::autosym`): the suggestion line, the
//! application of a proven group to the search with its cross-check, and
//! the labelling of a reduced run (start line, statistics suffix, `-stats`).

use std::process::ExitCode;
use std::time::{Duration, Instant};

use tlx_base::format::{self, JsonNewline};
use tlx_eval::model::autosym::{self, Analysis};
use tlx_eval::model::symcheck::{self, Bounds};
use tlx_eval::model::InterpModel;
use tlx_sema::optimize::{AUTOSYM_MAX_GROUPS, AUTOSYM_MAX_KEYS, AUTOSYM_MAX_ORDER};

use crate::args::Args;
use crate::out::{self, code};
use crate::stats;

/// The automatic symmetry of this run (docs/usage.md sections 6.2 and 6.3):
/// analyze the sets of model values; under `-tlc` print the suggestion; in
/// the default mode apply the proven group when that is allowed and name
/// the optimizations of the run. The symmetry applied, if any; an internal
/// error (exit 101) if the cross-check of the proof finds a witness.
pub fn run(model: &mut InterpModel, a: &Args) -> Result<Option<Applied>, ExitCode> {
    if a.checksymmetry {
        return Ok(None);
    }
    if a.simulate.is_some() || !model.has_behavior {
        if !a.tlc {
            if a.optimize {
                crate::proofs::emit(model, a.proofdir.as_deref(), None)?;
            }
            label(None);
        }
        return Ok(None);
    }
    let mut an = autosym::analyze(model);
    // Promote `CHOOSE`-rejected candidates only when a connected Lean
    // choice-symmetry certificate (`ChooseSymCertificate`) proves them statically.
    let mut precertified: Option<Precertified> = None;
    if (a.tlc || !a.noautosymmetry)
        && tlx_base::knobs::Env::process().string_or_default("TLX_AUTOSYM_FORCE").trim().is_empty()
        && model.live.is_empty()
        && not_applicable(model, &an).is_none()
        && an.sets.iter().any(|s| matches!(&s.choose_verdict, Some(autosym::Verdict::Proven { .. })))
    {
        precertified = promote_certified_choices(model, &mut an);
    }
    stats::phase("auto symmetry analysis", an.elapsed);
    report(&an);
    if a.tlc {
        // With a `VIEW`, TLC's verbatim path (least orbit state, then the view)
        // needs the view to be a symmetry-compatible encoding of the whole
        // state: only a full-retention tuple is a bijection. An omitting tuple's
        // certified composition is a default-mode reduction, not advice to
        // declare the group, so it gets no suggestion.
        if !model.has_view() || model.view_retains_all() {
            let cert_group = if model.live.is_empty() {
                if !an.group_text().is_empty() && not_applicable(model, &an).is_none() {
                    let text = match &precertified {
                        Some(pc) => Some(pc.group_text.clone()),
                        None => certify_groups(model, &eligible_proven(&an))
                            .map(|(sel, _)| sel.iter().filter_map(|s| s.group_text()).collect::<Vec<_>>().join(" x ")),
                    };
                    Some(text)
                } else {
                    Some(None)
                }
            } else {
                None
            };
            if let Some(line) = an.suggestion_for(cert_group.as_ref().map(|o| o.as_deref())) {
                out::info(code::GENERAL, &line);
            }
        }
        return Ok(None);
    }
    // Projection keeps priority when it composes with symmetry or reduces more
    // states. Pass eligible proven symmetry keys into state projection so
    // dead-field sentinels avoid moved keys and preserve VIEW equivariance.
    // When a projection does not compose with an eligible certified symmetry
    // group, compare both reduced graphs on a bounded probe so `-optimize`
    // does not displace a stronger certified symmetry.
    let sym_eligible = !a.noautosymmetry && not_applicable(model, &an).is_none();
    let eligible_sets = if sym_eligible { eligible_proven(&an) } else { Vec::new() };
    let sym_keys: std::collections::BTreeSet<std::sync::Arc<str>> = eligible_sets
        .iter()
        .flat_map(|s| {
            s.candidate.elems.iter().filter_map(|e| match e {
                tlx_value::Value::ModelValue(sym) => Some(std::sync::Arc::from(sym.as_str())),
                _ => None,
            })
        })
        .collect();
    let mut unprojected = (a.optimize && !eligible_sets.is_empty()).then(|| model.clone());
    let mut projection = a.optimize.then(|| model.project_state_with_sym_keys(&sym_keys)).flatten();
    let reusable = if projection.is_none() { precertified.take() } else { None };
    let stats_before_apply = tlx_runtime::stats::section("auto symmetry");
    let mut applied = apply(model, &mut an, a.noautosymmetry, reusable)?;
    if applied.is_none() && matches!(projection, Some(("phase-field-projection" | "threshold-counter-projection", _))) {
        let proj_rule = projection.as_ref().map(|(r, _)| *r).unwrap_or("projection");
        if let Some(mut sym_model) = unprojected.take() {
            let stats_after_proj_apply = tlx_runtime::stats::section("auto symmetry");
            restore_section("auto symmetry", stats_before_apply.as_deref());
            let mut an_sym = an.clone();
            let sym_applied = apply(&mut sym_model, &mut an_sym, false, precertified)?;
            if sym_applied.is_some() {
                let t0 = Instant::now();
                let keep_proj = match (
                    model.probe_reduced_size(COMPARE_PROBE_STATES, COMPARE_PROBE_DEPTH, COMPARE_PROBE_EDGES, COMPARE_PROBE_TIME),
                    sym_model.probe_reduced_size(COMPARE_PROBE_STATES, COMPARE_PROBE_DEPTH, COMPARE_PROBE_EDGES, COMPARE_PROBE_TIME),
                ) {
                    (Some(proj_probe), Some(sym_probe)) => projection_beats_sym(&proj_probe, &sym_probe),
                    _ => false,
                };
                stats::phase("projection vs symmetry probe", t0.elapsed());
                if !keep_proj {
                    note(&format!("{proj_rule}: not applied (bounded probe did not show fewer states than certified symmetry)"));
                    *model = sym_model;
                    projection = None;
                    applied = sym_applied;
                } else {
                    restore_section("auto symmetry", stats_after_proj_apply.as_deref());
                }
            } else {
                restore_section("auto symmetry", stats_after_proj_apply.as_deref());
            }
        }
    }
    if let Some((rule, omitted)) = projection {
        crate::proofs::emit(model, a.proofdir.as_deref(), Some((rule, &omitted)))?;
        let variables = omitted.join(", ");
        let arithmetic = match rule {
            "relative-age-projection" => "; mathematical clock arithmetic",
            "ordered-allocation-projection" => "; mathematical allocation arithmetic",
            "threshold-counter-projection" if model.mathematical_counter_arithmetic() => "; mathematical counter arithmetic",
            _ => "",
        };
        let group = applied.as_ref().map(|s| s.group.as_str()).or(model.ip.cfg.symmetry.as_deref());
        let combined = group.map(|g| format!(", composed with symmetry {g}")).unwrap_or_default();
        out::info(
            code::OPTIMIZATIONS_USED,
            &format!(
                "Optimizations: {rule} ({variables}; certificate generated; safety checks only{arithmetic}){combined}.\nCounts refer to the reduced search; run with -tlc for TLC-identical statistics."
            ),
        );
        out::set_reduced("optimization");
        let symmetry = group
            .map(|g| {
                format!(
                    r#"{{"name":"symmetry","scope":"safety","proof":"{}","preserved":["V-safe","CEX"],"detail":{}}},"#,
                    if applied.is_some() { "generated-lean" } else { "none" },
                    json_string(g)
                )
            })
            .unwrap_or_default();
        tlx_runtime::stats::set_json(
            "optimizations",
            format!(
                r#"[{symmetry}{{"name":"{rule}","scope":"safety","proof":"generated-lean","preserved":["V-safe","CEX"],"detail":{}}}]"#,
                json_string(&variables)
            ),
        );
    } else {
        if let Some(symmetry) = &applied {
            crate::proofs::emit(model, a.proofdir.as_deref(), Some(("keyed-symmetry", std::slice::from_ref(&symmetry.group))))?;
        } else if a.optimize {
            crate::proofs::emit(model, a.proofdir.as_deref(), None)?;
        }
        label(applied.as_ref());
    }
    Ok(applied)
}

/// Record every candidate with its result for `-stats`.
fn report(an: &Analysis) {
    let mut text = String::new();
    for s in an.proven() {
        text.push_str(&format!("{}: proven {}\n", s.candidate.name, s.group_text().unwrap_or_default()));
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

/// The largest certified group applied, and the largest factor it may have:
/// the certificate emitters' own bounds (`AUTOSYM_MAX_ORDER`,
/// `AUTOSYM_MAX_KEYS`). A factorized disjoint product is canonicalized per
/// state without enumerating `|G|` (`tlx-eval` partition refinement), so the
/// bound is the certificate emission and candidate-search cost.
const MAX_ORDER: u128 = AUTOSYM_MAX_ORDER;
const MAX_KEYS: usize = AUTOSYM_MAX_KEYS;

/// The maximum number of distinct model values in a product with order
/// `<= MAX_ORDER`: twelve disjoint order-2 factors (`2^12 = 4,096`) reach 24
/// keys, and no other combination of factorial orders up to 5,040 has more.
const MAX_USED_KEYS: usize = 24;

/// The time the bounded cross-check of an applied group may take.
const CROSS_CHECK_TIME: Duration = Duration::from_millis(20);

/// Bounds of the profitability probe of competing candidate factors: one
/// bounded walk of admitted states (filtered by state and action constraints)
/// to see which proven groups move states, without a second full cross-check
/// cost.
const EFFECT_PROBE_STATES: usize = 256;
const EFFECT_PROBE_DEPTH: u32 = 6;
const EFFECT_PROBE_EDGES: usize = 10_000;
const EFFECT_PROBE_TIME: Duration = Duration::from_millis(10);

/// Bounds for the bounded BFS comparison between an uncomposable
/// `phase-field-projection` and a competing certified automatic symmetry.
const COMPARE_PROBE_STATES: usize = 1024;
const COMPARE_PROBE_DEPTH: u32 = 8;
const COMPARE_PROBE_EDGES: usize = 20_000;
const COMPARE_PROBE_TIME: Duration = Duration::from_millis(20);

/// Return `true` only when the bounded probes affirmatively show that
/// `phase-field-projection` explores strictly fewer states than the competing
/// certified symmetry. Ties, timeouts, and inconclusive incomplete prefixes
/// keep the default certified symmetry.
fn projection_beats_sym(proj: &tlx_eval::model::ReducedProbe, sym: &tlx_eval::model::ReducedProbe) -> bool {
    match (proj.completed, sym.completed) {
        (true, true) | (true, false) => proj.distinct < sym.distinct,
        (false, true) => false,
        (false, false) => {
            let shared = proj.cumulative_by_depth.len().min(sym.cumulative_by_depth.len());
            shared > 0 && proj.cumulative_by_depth[shared - 1] < sym.cumulative_by_depth[shared - 1]
        }
    }
}

fn restore_section(name: &str, saved: Option<&str>) {
    tlx_runtime::stats::set_section(name, saved.unwrap_or_default().to_owned());
}

fn eligible_proven(an: &Analysis) -> Vec<&autosym::SetResult> {
    an.proven().filter(|s| s.group_order() <= MAX_ORDER).collect()
}

struct Precertified {
    names: Vec<String>,
    group_text: String,
    certificate: String,
}

/// Apply the proven symmetry of `an` to `model` when it is allowed: the
/// safety search only (no temporal properties), no VIEW, and no builtin whose
/// output or result depends on the states explored. A declared `.cfg`
/// `SYMMETRY` is enlarged when the proven candidates extend it
/// (`apply_augmented`); otherwise no automatic group is applied. Before an
/// automatic group is installed, a bounded check of it runs as a cross-check
/// of the proof; a witness is an internal error (exit 101).
fn apply(model: &mut InterpModel, an: &mut Analysis, off: bool, precertified: Option<Precertified>) -> Result<Option<Applied>, ExitCode> {
    let forced = tlx_base::knobs::Env::process().string_or_default("TLX_AUTOSYM_FORCE");
    let forced: Vec<&str> = forced.split(',').map(str::trim).filter(|n| !n.is_empty()).collect();
    if off {
        note("not applied: -noautosymmetry");
        return Ok(None);
    }
    an.force(&forced);
    if model.ip.cfg.symmetry.is_some() {
        if let Some(why) = not_applicable_with(model, an, true) {
            note(&format!("not applied: {why}"));
            return Ok(None);
        }
        return apply_augmented(model, an);
    }
    if let Some(why) = not_applicable(model, an) {
        note(&format!("not applied: {why}"));
        return Ok(None);
    }
    let proven: Vec<&autosym::SetResult> = an.proven().collect();
    if proven.is_empty() {
        return Ok(None);
    }
    let eligible = eligible_proven(an);
    for s in proven.iter().filter(|s| s.group_order() > MAX_ORDER) {
        note(&format!("{}: not applied (the group would have more than {MAX_ORDER} elements)", s.candidate.name));
    }
    if eligible.is_empty() {
        return Ok(None);
    }
    let mut precertified = precertified;
    // A certified group whose permutations fix every admitted state the
    // bounded probe reaches reduces nothing, yet its larger order can keep a
    // smaller productive group out of the selected product. When competing
    // proven factors did not all fit in the selected product, measure every
    // competing factor against one shared bounded sample of admitted states
    // (filtered by state and action constraints); if an inert selected factor
    // displaces an unselected productive factor, leave the inert factor out
    // and certify the next product. The movement probe is evidence, not a
    // proof; not applying a proven symmetry stays sound.
    let mut movement: Option<Vec<bool>> = None;
    let mut excluded: Vec<String> = Vec::new();
    let mut fallback: Option<(Vec<&autosym::SetResult>, String)> = None;
    let mut pending_notes: Vec<String> = Vec::new();
    let (selected, certificate) = loop {
        let remaining: Vec<&autosym::SetResult> = eligible.iter().copied().filter(|s| !excluded.contains(&s.candidate.name)).collect();
        let reused = if forced.is_empty() {
            precertified.take().and_then(|pc| {
                let sel = pc
                    .names
                    .iter()
                    .map(|name| remaining.iter().copied().find(|s| s.candidate.name == *name))
                    .collect::<Option<Vec<_>>>()?;
                Some((sel, pc.certificate))
            })
        } else {
            None
        };
        let Some((selected, certificate)) = reused.or_else(|| certify_groups(model, &remaining)) else {
            if let Some(prev) = fallback.take() {
                pending_notes.clear();
                break prev;
            }
            if model.has_view() {
                note("not applied: no connected Lean certificate covers automatic symmetry over the cfg VIEW (an omitted variable may be live in a retained predicate or update)");
            } else {
                note("not applied: no connected Lean certificate for automatic symmetry");
            }
            return Ok(None);
        };
        let unselected: Vec<&autosym::SetResult> =
            remaining.iter().copied().filter(|s| s.full() && !selected.iter().any(|chosen| std::ptr::eq(*s, *chosen))).collect();
        if !unselected.is_empty() {
            let moved = match &movement {
                Some(m) => m,
                None => {
                    let group_gens: Vec<Vec<_>> = eligible.iter().map(|s| s.generators()).collect();
                    let bounds = Bounds {
                        states: EFFECT_PROBE_STATES,
                        depth: EFFECT_PROBE_DEPTH,
                        edges: EFFECT_PROBE_EDGES,
                        time: Some(EFFECT_PROBE_TIME),
                        ..Bounds::default()
                    };
                    let t0 = Instant::now();
                    let res = symcheck::probe_movement(model, &group_gens, &bounds);
                    stats::phase("auto symmetry effect probe", t0.elapsed());
                    let m = res.unwrap_or_else(|_| vec![true; eligible.len()]);
                    movement.insert(m)
                }
            };
            let is_moved = |s: &autosym::SetResult| eligible.iter().position(|e| std::ptr::eq(*e, s)).is_none_or(|idx| moved[idx]);
            let inert: Vec<&autosym::SetResult> = selected.iter().copied().filter(|s| !is_moved(s)).collect();
            let displaced = !inert.is_empty() && unselected.iter().any(|s| is_moved(s));
            if displaced {
                for s in &inert {
                    pending_notes.push(format!(
                        "{}: not applied (its permutations fix every admitted state the bounded probe reached, and it would displace a productive group)",
                        s.candidate.name
                    ));
                    excluded.push(s.candidate.name.clone());
                }
                if fallback.is_none() {
                    fallback = Some((selected, certificate));
                }
                continue;
            }
        }
        break (selected, certificate);
    };
    for line in pending_notes {
        note(&line);
    }
    let gens: Vec<_> = selected.iter().flat_map(|s| s.generators()).collect();
    let text = selected.iter().filter_map(|s| s.group_text()).collect::<Vec<_>>().join(" x ");
    let bounds = Bounds { time: Some(CROSS_CHECK_TIME), ..Bounds::default() };
    let t0 = Instant::now();
    let check = symcheck::check_perms(model, gens.clone(), &bounds);
    stats::phase("auto symmetry cross-check", t0.elapsed());
    match check {
        Ok(r) => {
            if let Some(w) = r.witness {
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
        Err(e) => {
            note(&format!("not applied: cross-check failed ({})", e.message));
            return Ok(None);
        }
    }
    if let Err(e) = model.apply_symmetry(gens) {
        note(&format!("not applied: {}", e.message));
        return Ok(None);
    }
    // A declared tuple `VIEW` that omits certified-erasable variables is keyed
    // by the orbit of the projected value (the composed certificate's key)
    // instead of a whole-state least representative, which would refine the
    // certified quotient and could lose counterexample replay.
    if model.tuple_view_vars().is_some() && !model.view_retains_all() {
        model.install_view_projection();
    }
    model.record_symmetry_certificate(certificate);
    Ok(Some(Applied { group: text }))
}

/// In the default mode, enlarge a declared `.cfg` `SYMMETRY` with additional
/// automatically proven groups. The declared group must factor as a disjoint
/// product of full symmetric groups; every added candidate must be a proven
/// full group disjoint from it, and the combined product must stay within the
/// certificate emitters' bounds. One connected Lean certificate covers the
/// whole combined product; without it the declared group stays untouched
/// (fail closed).
fn apply_augmented(model: &mut InterpModel, an: &mut Analysis) -> Result<Option<Applied>, ExitCode> {
    let declared_factors: Vec<Vec<tlx_value::SymAtom>> = match model.symmetry_factors() {
        Some(factors) => factors.into_iter().map(<[tlx_value::SymAtom]>::to_vec).collect(),
        None => {
            note("not applied: the declared SYMMETRY is not a disjoint product of full symmetric groups");
            return Ok(None);
        }
    };
    let declared_order = declared_factors.iter().fold(1u128, |o, f| o.saturating_mul(order_of(f.len())));
    if declared_order > MAX_ORDER {
        note(&format!("not applied: the declared SYMMETRY product has order {declared_order}, above the certificate bound {MAX_ORDER}"));
        return Ok(None);
    }
    let declared_atoms: std::collections::HashSet<tlx_value::SymAtom> = declared_factors.iter().flatten().copied().collect();
    let declared_names: Vec<(Vec<String>, String)> =
        declared_factors.iter().map(|keys| (key_names(keys), declared_factor_text(an, keys))).collect();
    // Proven full candidates whose elements the declared group does not move.
    let mut extra: Vec<&autosym::SetResult> = an
        .proven()
        .filter(|s| {
            s.full()
                && s.candidate.elems.len() <= MAX_KEYS
                && (2..=MAX_ORDER).contains(&s.group_order())
                && s.candidate
                    .elems
                    .iter()
                    .all(|e| matches!(e, tlx_value::Value::ModelValue(m) if !declared_atoms.contains(&tlx_value::SymAtom::Model(*m))))
        })
        .collect();
    if extra.is_empty() {
        note("not applied: no proven symmetry group is disjoint from the declared SYMMETRY");
        return Ok(None);
    }
    // Prefer the largest groups, in cfg order on ties, while the combined
    // product stays disjoint and within the emitters' bounds.
    let at = |s: &&autosym::SetResult| an.sets.iter().position(|x| std::ptr::eq(x, *s)).unwrap_or(usize::MAX);
    extra.sort_by(|a, b| b.group_order().cmp(&a.group_order()).then_with(|| at(a).cmp(&at(b))));
    let mut used = declared_atoms;
    let mut chosen: Vec<&autosym::SetResult> = Vec::new();
    let mut order = declared_order;
    for s in extra {
        let keys = candidate_keys(s);
        let next_order = order.saturating_mul(s.group_order());
        if declared_factors.len() + chosen.len() + 1 > AUTOSYM_MAX_GROUPS || next_order > MAX_ORDER || keys.iter().any(|m| used.contains(m))
        {
            continue;
        }
        order = next_order;
        used.extend(keys);
        chosen.push(s);
    }
    if chosen.is_empty() {
        note("not applied: no proven symmetry group fits the combined group bounds");
        return Ok(None);
    }
    let mut combined_names: Vec<Vec<String>> = declared_names.iter().map(|(names, _)| names.clone()).collect();
    let mut text: Vec<String> = declared_names.into_iter().map(|(_, t)| t).collect();
    let mut factors = declared_factors;
    for s in &chosen {
        let keys = candidate_keys(s);
        combined_names.push(key_names(&keys));
        text.extend(s.group_text());
        factors.push(keys);
    }
    let Some(certificate) = model.augmented_symmetry_certificate(&combined_names) else {
        note("not applied: no connected Lean certificate for the declared SYMMETRY superset");
        return Ok(None);
    };
    let added_text = chosen.iter().filter_map(|s| s.group_text()).collect::<Vec<_>>().join(" x ");
    let extra_gens: Vec<_> = chosen.iter().flat_map(|s| s.generators()).collect();
    let bounds = Bounds { time: Some(CROSS_CHECK_TIME), ..Bounds::default() };
    let t0 = Instant::now();
    let check = symcheck::check_perms(model, extra_gens.clone(), &bounds);
    stats::phase("auto symmetry cross-check", t0.elapsed());
    match check {
        Ok(r) => {
            if let Some(w) = r.witness {
                out::error(
                    code::GENERAL,
                    &format!(
                        "Internal error: the symmetry {added_text} that tlx added to the declared SYMMETRY does not hold ({}; permutation {}). Run with -noautosymmetry.",
                        w.part,
                        w.permutation
                    ),
                );
                return Err(ExitCode::from(101));
            }
        }
        Err(e) => {
            note(&format!("not applied: cross-check failed ({})", e.message));
            return Ok(None);
        }
    }
    if let Err(e) = model.install_augmented_symmetry(factors, extra_gens, certificate) {
        note(&format!("not applied: {}", e.message));
        return Ok(None);
    }
    Ok(Some(Applied { group: text.join(" x ") }))
}

/// `n!`, saturating (a full symmetric group over `n` model values).
fn order_of(n: usize) -> u128 {
    (1..=n as u128).fold(1u128, |a, k| a.saturating_mul(k))
}

/// The model values of a proven candidate, in cfg order.
fn candidate_keys(s: &autosym::SetResult) -> Vec<tlx_value::SymAtom> {
    s.candidate
        .elems
        .iter()
        .filter_map(|e| match e {
            tlx_value::Value::ModelValue(m) => Some(tlx_value::SymAtom::Model(*m)),
            _ => None,
        })
        .collect()
}

fn key_names(keys: &[tlx_value::SymAtom]) -> Vec<String> {
    keys.iter().map(|m| m.sym().as_str().to_owned()).collect()
}

/// TLA+ text of a factor of the declared group: the cfg constant that names
/// the same model values when there is one, the explicit set otherwise.
fn declared_factor_text(an: &Analysis, keys: &[tlx_value::SymAtom]) -> String {
    let named = an.sets.iter().find(|s| {
        s.candidate.elems.len() == keys.len()
            && s.candidate
                .elems
                .iter()
                .all(|e| matches!(e, tlx_value::Value::ModelValue(m) if keys.contains(&tlx_value::SymAtom::Model(*m))))
    });
    match named {
        Some(s) => format!("Permutations({})", s.candidate.name),
        None => format!("Permutations({{{}}})", keys.iter().map(|m| m.sym().as_str()).collect::<Vec<_>>().join(", ")),
    }
}

#[derive(Clone)]
struct CandGroup<'a> {
    orig_idx: usize,
    cand: &'a autosym::SetResult,
    ord: u16,
    keys: Vec<String>,
    // Every accepted full symmetric group has `2..=MAX_KEYS` keys.
    key_ids: [u32; MAX_KEYS],
    key_len: u8,
}

impl CandGroup<'_> {
    fn id_slice(&self) -> &[u32] {
        &self.key_ids[..self.key_len as usize]
    }
}

#[derive(Clone, Copy)]
struct SearchNode {
    upper: u16,
    is_leaf: bool,
    cur_ord: u16,
    len: u8,
    // One entry per selected factor (`AUTOSYM_MAX_GROUPS` factors at most).
    idxs: [usize; AUTOSYM_MAX_GROUPS],
    start: usize,
    // The union of the selected factors' keys (at most `MAX_USED_KEYS`).
    used: [u32; MAX_USED_KEYS],
    used_len: u8,
}

impl SearchNode {
    fn used_slice(&self) -> &[u32] {
        &self.used[..self.used_len as usize]
    }

    fn cmp_key(&self, other: &Self) -> std::cmp::Ordering {
        self.upper
            .cmp(&other.upper)
            .then_with(|| self.is_leaf.cmp(&other.is_leaf))
            .then_with(|| self.cur_ord.cmp(&other.cur_ord))
            .then_with(|| self.len.cmp(&other.len))
            .then_with(|| other.idxs[..other.len as usize].cmp(&self.idxs[..self.len as usize]))
            .then_with(|| other.start.cmp(&self.start))
    }
}

impl PartialEq for SearchNode {
    fn eq(&self, other: &Self) -> bool {
        self.cmp_key(other) == std::cmp::Ordering::Equal
    }
}

impl Eq for SearchNode {}

impl Ord for SearchNode {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.cmp_key(other)
    }
}

impl PartialOrd for SearchNode {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

fn ids_disjoint(used: &[u32], cand_ids: &[u32]) -> bool {
    !cand_ids.iter().any(|id| used.contains(id))
}

/// Admissible upper bound (`<= MAX_ORDER`) on the maximum product order achievable by extending
/// `cur_ord` with mutually-disjoint candidates from `full[start..]` disjoint from `used`.
fn attainable_order(cur_ord: u16, start: usize, used: &[u32], full: &[CandGroup<'_>], next_bucket: &[usize]) -> u16 {
    const CAP: usize = MAX_ORDER as usize;
    if start >= full.len() || (cur_ord as usize) * (full[full.len() - 1].ord as usize) > CAP {
        return cur_ord;
    }
    let mut reach = [false; CAP + 1];
    reach[cur_ord as usize] = true;
    let mut best = cur_ord;
    let mut i = start;
    while i < full.len() {
        let ord = full[i].ord as usize;
        let end = next_bucket[i];
        if (cur_ord as usize) * ord <= CAP {
            // The most factors of this order a product `<= CAP` can hold.
            let bucket_cap = match ord {
                5040 | 720 | 120 => 1,
                24 => 2,
                6 => 4,
                _ => 12,
            };
            let mut found = 0usize;
            for item in &full[i..end] {
                if ids_disjoint(used, item.id_slice()) {
                    for p in (cur_ord as usize..=CAP / ord).rev() {
                        if reach[p] {
                            let np = p * ord;
                            reach[np] = true;
                            if np as u16 > best {
                                best = np as u16;
                            }
                        }
                    }
                    if best == MAX_ORDER as u16 {
                        return best;
                    }
                    found += 1;
                    if found == bucket_cap {
                        break;
                    }
                }
            }
        }
        i = end;
    }
    best
}

fn search_product_subset<'a, F: FnMut(&[Vec<String>]) -> Option<String>>(
    certify: &mut F,
    tried_products: &mut std::collections::HashSet<Vec<usize>>,
    full: &[CandGroup<'a>],
    (min_len, min_ord): (u8, u16),
    (max_pops, max_attempts): (usize, usize),
) -> (Option<(Vec<&'a autosym::SetResult>, String)>, bool) {
    let mut next_bucket = vec![full.len(); full.len()];
    for i in (0..full.len()).rev() {
        next_bucket[i] = if i + 1 < full.len() && full[i + 1].ord == full[i].ord { next_bucket[i + 1] } else { i + 1 };
    }

    // Best-first A* branch-and-bound ranked by admissible attainable product order (`<= MAX_ORDER`),
    // using binary `(take, skip)` branching so heap size stays O(pops) rather than O(N^2).
    let floor_ord = min_ord.max(2);
    let root_upper = attainable_order(1, 0, &[], full, &next_bucket);
    if root_upper < floor_ord {
        return (None, false);
    }
    let mut heap = std::collections::BinaryHeap::new();
    heap.push(SearchNode {
        upper: root_upper,
        is_leaf: false,
        cur_ord: 1,
        len: 0,
        idxs: [0; AUTOSYM_MAX_GROUPS],
        start: 0,
        used: [0; MAX_USED_KEYS],
        used_len: 0,
    });

    let mut pops = 0usize;
    let mut cert_attempts = 0usize;
    let mut budget_exhausted = false;
    while let Some(mut node) = heap.pop() {
        if node.upper < floor_ord {
            break;
        }
        if node.is_leaf {
            let mut chosen_idxs = node.idxs[..node.len as usize].to_vec();
            chosen_idxs.sort_by_key(|&i| full[i].orig_idx);
            let orig_key: Vec<usize> = chosen_idxs.iter().map(|&i| full[i].orig_idx).collect();
            if !tried_products.insert(orig_key) {
                continue;
            }
            let groups: Vec<Vec<String>> = chosen_idxs.iter().map(|&i| full[i].keys.clone()).collect();
            cert_attempts += 1;
            if let Some(cert) = certify(&groups) {
                let selected = chosen_idxs.into_iter().map(|i| full[i].cand).collect();
                return (Some((selected, cert)), false);
            }
            if cert_attempts >= max_attempts {
                budget_exhausted = true;
                break;
            }
            continue;
        }
        pops += 1;
        if pops > max_pops {
            budget_exhausted = true;
            break;
        }
        while node.start < full.len()
            && ((node.cur_ord as u128) * (full[node.start].ord as u128) > MAX_ORDER
                || !ids_disjoint(node.used_slice(), full[node.start].id_slice()))
        {
            node.start += 1;
        }
        if node.start >= full.len() {
            if node.len >= min_len && node.cur_ord >= floor_ord {
                node.upper = node.cur_ord;
                node.is_leaf = true;
                heap.push(node);
            }
            continue;
        }
        let s = node.start;
        let next_ord = node.cur_ord * full[s].ord;
        let mut next_idxs = node.idxs;
        next_idxs[node.len as usize] = s;
        let next_len = node.len + 1;
        let mut next_used = node.used;
        let cand_ids = full[s].id_slice();
        let next_used_len = node.used_len as usize + cand_ids.len();
        debug_assert!(next_used_len <= MAX_USED_KEYS, "a product of order <= {MAX_ORDER} has at most {MAX_USED_KEYS} keys");
        next_used[node.used_len as usize..next_used_len].copy_from_slice(cand_ids);
        let up_take = attainable_order(next_ord, s + 1, &next_used[..next_used_len], full, &next_bucket);
        if up_take >= floor_ord && (next_len >= min_len || up_take > next_ord) {
            heap.push(SearchNode {
                upper: up_take,
                is_leaf: next_len >= min_len && up_take == next_ord,
                cur_ord: next_ord,
                len: next_len,
                idxs: next_idxs,
                start: s + 1,
                used: next_used,
                used_len: next_used_len as u8,
            });
        }

        let up_skip = attainable_order(node.cur_ord, s + 1, node.used_slice(), full, &next_bucket);
        if up_skip >= floor_ord && (node.len >= min_len || up_skip > node.cur_ord) {
            node.upper = up_skip;
            node.is_leaf = node.len >= min_len && up_skip == node.cur_ord;
            node.start = s + 1;
            heap.push(node);
        }
    }
    (None, budget_exhausted)
}

fn fallback_certify_groups<'a, F: FnMut(&[Vec<String>]) -> Option<String>>(
    certify: &mut F,
    tried_products: &mut std::collections::HashSet<Vec<usize>>,
    full: &[CandGroup<'a>],
    max_pops: usize,
    max_attempts: usize,
) -> Option<(Vec<&'a autosym::SetResult>, String)> {
    // When uncertifiable high-order combinations exhaust the primary product budget, probe
    // remaining singletons (returning immediately if a singleton reaches `MAX_ORDER`, otherwise
    // retaining only the single highest-order Lean string), re-run product search skipping
    // already-failed products, and greedily extend the best singleton if secondary top-down
    // combinations also exhaust the budget.
    const MAX_SINGLETON_PROBES: usize = 256;
    let mut probes = 0usize;
    let mut cert_indices: Vec<usize> = Vec::new();
    let mut best_singleton: Option<(usize, String)> = None;
    for (i, item) in full.iter().enumerate() {
        if !tried_products.insert(vec![item.orig_idx]) {
            continue;
        }
        if probes >= MAX_SINGLETON_PROBES {
            break;
        }
        probes += 1;
        if let Some(cert) = certify(std::slice::from_ref(&item.keys)) {
            if (item.ord as u128) >= MAX_ORDER {
                return Some((vec![item.cand], cert));
            }
            cert_indices.push(i);
            if best_singleton.is_none() {
                best_singleton = Some((i, cert));
            }
        }
    }
    let (best_idx, best_cert) = best_singleton?;
    let best_ord = full[best_idx].ord;
    if cert_indices.len() >= 2 && (best_ord as u128) < MAX_ORDER {
        let cert_sub: Vec<CandGroup<'a>> = cert_indices.iter().map(|&i| full[i].clone()).collect();
        let (prod, sec_exhausted) =
            search_product_subset(certify, tried_products, &cert_sub, (2, best_ord.saturating_add(1)), (max_pops, max_attempts));
        if let Some(found) = prod {
            return Some(found);
        }
        if sec_exhausted {
            let mut acc_idxs = vec![best_idx];
            let mut acc_ord = best_ord;
            let mut acc_used: Vec<u32> = full[best_idx].id_slice().to_vec();
            let mut acc_cert = best_cert;
            for &ci in &cert_indices {
                if ci == best_idx || (acc_ord as u128) * (full[ci].ord as u128) > MAX_ORDER || !ids_disjoint(&acc_used, full[ci].id_slice())
                {
                    continue;
                }
                let mut trial = acc_idxs.clone();
                trial.push(ci);
                trial.sort_by_key(|&i| full[i].orig_idx);
                let orig_key: Vec<usize> = trial.iter().map(|&i| full[i].orig_idx).collect();
                if !tried_products.insert(orig_key) {
                    continue;
                }
                let groups: Vec<Vec<String>> = trial.iter().map(|&i| full[i].keys.clone()).collect();
                if let Some(cert) = certify(&groups) {
                    acc_idxs = trial;
                    acc_ord *= full[ci].ord;
                    acc_used.extend_from_slice(full[ci].id_slice());
                    acc_cert = cert;
                }
            }
            return Some((acc_idxs.into_iter().map(|i| full[i].cand).collect(), acc_cert));
        }
    }
    Some((vec![full[best_idx].cand], best_cert))
}

fn certify_groups<'a>(model: &InterpModel, chosen: &[&'a autosym::SetResult]) -> Option<(Vec<&'a autosym::SetResult>, String)> {
    certify_groups_by(chosen, 16_384, 1_024, |groups| model.symmetry_certificate(groups))
}

fn certify_choose_groups<'a>(model: &InterpModel, chosen: &[&'a autosym::SetResult]) -> Option<(Vec<&'a autosym::SetResult>, String)> {
    certify_groups_by(chosen, 16_384, 1_024, |groups| model.choose_symmetry_certificate(groups))
}

fn certify_groups_by<'a, F: FnMut(&[Vec<String>]) -> Option<String>>(
    chosen: &[&'a autosym::SetResult],
    max_pops: usize,
    max_attempts: usize,
    mut certify: F,
) -> Option<(Vec<&'a autosym::SetResult>, String)> {
    let mut raw: Vec<(usize, &'a autosym::SetResult, u16, Vec<String>)> = chosen
        .iter()
        .enumerate()
        .filter_map(|(orig_idx, &cand)| {
            if !cand.full() {
                return None;
            }
            let ord = u16::try_from(cand.group_order()).ok().filter(|&o| (2..=MAX_ORDER as u16).contains(&o))?;
            let keys = cand
                .candidate
                .elems
                .iter()
                .map(|v| match v {
                    tlx_value::Value::ModelValue(k) => Some(k.as_str().to_owned()),
                    _ => None,
                })
                .collect::<Option<Vec<_>>>()
                .filter(|ks| ks.len() <= MAX_KEYS)?;
            Some((orig_idx, cand, ord, keys))
        })
        .collect();
    if raw.is_empty() {
        return None;
    }
    raw.sort_by(|a, b| b.2.cmp(&a.2).then_with(|| a.0.cmp(&b.0)));

    let mut key_map: std::collections::HashMap<&'a str, u32> = std::collections::HashMap::new();
    for (_, cand, _, _) in &raw {
        for v in &cand.candidate.elems {
            if let tlx_value::Value::ModelValue(k) = v {
                let next_id = u32::try_from(key_map.len()).expect("key count fits u32");
                key_map.entry(k.as_str()).or_insert(next_id);
            }
        }
    }
    let full: Vec<CandGroup<'a>> = raw
        .into_iter()
        .map(|(orig_idx, cand, ord, keys)| {
            let mut key_ids = [0u32; MAX_KEYS];
            for (slot, k) in key_ids.iter_mut().zip(&keys) {
                *slot = key_map[k.as_str()];
            }
            let key_len = keys.len() as u8;
            CandGroup { orig_idx, cand, ord, keys, key_ids, key_len }
        })
        .collect();

    let mut tried_products = std::collections::HashSet::new();
    let (found, budget_exhausted) = search_product_subset(&mut certify, &mut tried_products, &full, (1, 2), (max_pops, max_attempts));
    if found.is_some() {
        return found;
    }
    if !budget_exhausted {
        return None;
    }
    fallback_certify_groups(&mut certify, &mut tried_products, &full, max_pops, max_attempts)
}

fn promote_certified_choices(model: &InterpModel, an: &mut Analysis) -> Option<Precertified> {
    let mut trial = an.clone();
    let mut has_promotable = false;
    for s in &mut trial.sets {
        if let Some(v @ autosym::Verdict::Proven { .. }) = &s.choose_verdict {
            s.verdict = v.clone();
            has_promotable = true;
        }
    }
    if !has_promotable {
        return None;
    }
    let eligible = eligible_proven(&trial);
    let (selected, certificate) = certify_choose_groups(model, &eligible)?;
    let names: Vec<String> = selected.iter().map(|s| s.candidate.name.clone()).collect();
    let certified_names: std::collections::HashSet<&str> = names.iter().map(String::as_str).collect();
    let mut promoted_any = false;
    for s in &mut an.sets {
        if certified_names.contains(s.candidate.name.as_str()) {
            if let Some(v @ autosym::Verdict::Proven { .. }) = &s.choose_verdict {
                s.verdict = v.clone();
                promoted_any = true;
            }
        }
    }
    if !promoted_any {
        return None;
    }
    let all_eligible_covered =
        an.proven().filter(|s| s.group_order() <= MAX_ORDER && s.full()).all(|s| certified_names.contains(s.candidate.name.as_str()));
    if !all_eligible_covered {
        return None;
    }
    let group_text = selected.iter().filter_map(|s| s.group_text()).collect::<Vec<_>>().join(" x ");
    Some(Precertified { names, group_text, certificate })
}

/// A symmetry applied to the search.
pub struct Applied {
    /// The group, as TLA+ text (`Permutations(RM) x Permutations(Acceptor)`).
    pub group: String,
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
    out::info(
        code::OPTIMIZATIONS_USED,
        &format!(
            "Optimizations: symmetry {} (certificate generated; safety checks only).\nCounts refer to the reduced search; run with -tlc for TLC-identical statistics.",
            a.group
        ),
    );
    out::set_reduced("symmetry");
    let json = format!(
        "[{{\"name\":\"symmetry\",\"scope\":\"safety\",\"proof\":\"generated-lean\",\"preserved\":[\"V-safe\",\"CEX\"],\"detail\":{}}}]",
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
    not_applicable_with(model, an, false)
}

/// Like [`not_applicable`]; `allow_declared` permits a declared `.cfg`
/// `SYMMETRY` when the caller certifies a superset of it instead of keeping
/// the declaration verbatim.
fn not_applicable_with(model: &InterpModel, an: &Analysis, allow_declared: bool) -> Option<String> {
    if !allow_declared && (!model.symmetry_maps().is_empty() || model.ip.cfg.symmetry.is_some()) {
        return Some("the cfg declares a SYMMETRY".into());
    }
    if model.has_view() && !model.has_automatic_projection() {
        // A declared tuple `VIEW` that is a permutation of the state variables
        // is a bijection on states, and one that omits variables composes with
        // certified erasure; both are certified below. Any other view, and any
        // view under a declared verbatim `SYMMETRY`, keeps the original search.
        if model.ip.cfg.symmetry.is_some() {
            return Some("the cfg has a VIEW".into());
        }
        if model.tuple_view_vars().is_none() {
            return Some("the cfg VIEW is not a tuple of distinct state variables".into());
        }
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

    fn mk_proven(name: &str, elems: &[&str]) -> autosym::SetResult {
        let vals: Vec<tlx_value::Value> = elems.iter().map(|s| tlx_value::Value::ModelValue(tlx_value::Sym::new(s))).collect();
        autosym::SetResult {
            candidate: autosym::Candidate { name: name.into(), elems: vals.clone() },
            verdict: autosym::Verdict::Proven { classes: vec![vals], pinned_by: Vec::new() },
            choose_verdict: None,
        }
    }

    #[test]
    fn fallback_never_discards_higher_order_singleton_for_smaller_product() {
        // Case 1: Two order-5040 (`MAX_ORDER`) singletons `Big1`/`Big2` where the first
        // exhausts a one-attempt primary budget, plus disjoint order-2 pair `P1 x P2`
        // (order 4). The fallback must return the certifiable order-5040 singleton
        // immediately, without probing `P1`, `P2`, or `[P1, P2]`.
        let u1 = mk_proven("U1", &["u1a", "u1b", "u1c", "u1d", "u1e", "u1f"]);
        let u2 = mk_proven("U2", &["u2a", "u2b", "u2c", "u2d", "u2e", "u2f"]);
        let big1 = mk_proven("Big1", &["a1", "a2", "a3", "a4", "a5", "a6", "a7"]);
        let big2 = mk_proven("Big2", &["b1", "b2", "b3", "b4", "b5", "b6", "b7"]);
        let p1 = mk_proven("P1", &["p1a", "p1b"]);
        let p2 = mk_proven("P2", &["p2a", "p2b"]);
        let refs = [&u1, &u2, &big1, &big2, &p1, &p2];
        let mut post_big_probed = false;
        let (sel, cert) = certify_groups_by(&refs, 16_384, 1, |gs| match gs {
            [g] if g[0] == "b1" => Some("cert-big2-5040".into()),
            [g] if g[0] == "p1a" || g[0] == "p2a" => {
                post_big_probed = true;
                Some("cert-p-2".into())
            }
            [g1, g2] if g1[0] == "p1a" && g2[0] == "p2a" => {
                post_big_probed = true;
                Some("cert-p1p2-4".into())
            }
            _ => None,
        })
        .unwrap();
        assert_eq!(sel.len(), 1);
        assert_eq!(sel[0].candidate.name, "Big2");
        assert_eq!(cert, "cert-big2-5040");
        assert!(!post_big_probed, "an order-5040 singleton must return immediately without probing smaller singletons or products");

        // Case 2: Order-120 singleton `Best` (which fails to combine with `P1`/`P2`) + `P1 x P2`
        // (order 4 < 120). Must keep `Best` (120), never overwriting it with `P1 x P2` (4).
        let f1 = mk_proven("F1", &["f1a", "f1b", "f1c", "f1d", "f1e", "f1f"]);
        let f2 = mk_proven("F2", &["f2a", "f2b", "f2c", "f2d", "f2e", "f2f"]);
        let best = mk_proven("Best", &["m1", "m2", "m3", "m4", "m5"]);
        let refs2 = [&f1, &f2, &best, &p1, &p2];
        let (sel2, cert2) = certify_groups_by(&refs2, 16_384, 2, |gs| match gs {
            [g] if g[0] == "m1" => Some("cert-best-120".into()),
            [g] if g[0] == "p1a" || g[0] == "p2a" => Some("cert-p-2".into()),
            [g1, g2] if g1[0] == "p1a" && g2[0] == "p2a" => Some("cert-p1p2-4".into()),
            _ => None,
        })
        .unwrap();
        assert_eq!(sel2.len(), 1);
        assert_eq!(sel2[0].candidate.name, "Best");
        assert_eq!(cert2, "cert-best-120");

        // Case 3: Order-6 singleton `Mid` (which fails to combine with `Q1`/`Q2`) + `Q1 x Q2`
        // (order 36 > 6). Must upgrade to `Q1 x Q2` (order 36) after checking `[Mid, Q1, Q2]`,
        // `[Mid, Q1]`, and `[Mid, Q2]`.
        let f3 = mk_proven("F3", &["f3a", "f3b", "f3c", "f3d", "f3e", "f3f"]);
        let f4 = mk_proven("F4", &["f4a", "f4b", "f4c", "f4d", "f4e", "f4f"]);
        let q1 = mk_proven("Q1", &["q1a", "q1b", "q1c"]);
        let q2 = mk_proven("Q2", &["q2a", "q2b", "q2c"]);
        let mid = mk_proven("Mid", &["s1", "s2", "s3"]);
        let refs3 = [&f1, &f2, &f3, &f4, &mid, &q1, &q2];
        let (sel3, cert3) = certify_groups_by(&refs3, 16_384, 4, |gs| match gs {
            [g] if g[0] == "s1" => Some("cert-mid-6".into()),
            [g] if g[0] == "q1a" || g[0] == "q2a" => Some("cert-q-6".into()),
            [g1, g2] if g1[0] == "q1a" && g2[0] == "q2a" => Some("cert-q1q2-36".into()),
            _ => None,
        })
        .unwrap();
        assert_eq!(sel3.iter().map(|s| s.candidate.name.as_str()).collect::<Vec<_>>(), vec!["Q1", "Q2"]);
        assert_eq!(cert3, "cert-q1q2-36");

        // Case 4: 15 disjoint order-2 candidates (`C(15, 9) = 5,005` order-512 products)
        // where all singletons and pairs (`len <= 2`) certify while `len >= 3` fails. Must never
        // retry any failed product across searches and must recover a certifiable pair (`order 4`).
        let bin: Vec<autosym::SetResult> = (1..=15).map(|i| mk_proven(&format!("B{i}"), &[&format!("b{i}a"), &format!("b{i}b")])).collect();
        let bin_refs: Vec<&autosym::SetResult> = bin.iter().collect();
        let mut seen_queries = std::collections::HashSet::new();
        let (sel4, cert4) = certify_groups_by(&bin_refs, 16_384, 1_024, |gs| {
            assert!(seen_queries.insert(gs.to_vec()), "duplicate certification query: {gs:?}");
            (gs.len() <= 2).then(|| format!("cert-len-{}", gs.len()))
        })
        .unwrap();
        assert_eq!(sel4.iter().map(|s| s.candidate.name.as_str()).collect::<Vec<_>>(), vec!["B1", "B2"]);
        assert_eq!(cert4, "cert-len-2");
    }

    #[test]
    fn projection_probe_keeps_symmetry_on_inconclusive_or_tied_prefixes() {
        use tlx_eval::model::ReducedProbe;
        // Measured projection win (both completed, e.g., 2-actor 9 vs 10): projection wins.
        assert!(projection_beats_sym(
            &ReducedProbe { distinct: 9, completed: true, cumulative_by_depth: vec![1, 5, 9] },
            &ReducedProbe { distinct: 10, completed: true, cumulative_by_depth: vec![1, 5, 10] },
        ));
        // Equal completed tie: keep default symmetry.
        assert!(!projection_beats_sym(
            &ReducedProbe { distinct: 10, completed: true, cumulative_by_depth: vec![1, 5, 10] },
            &ReducedProbe { distinct: 10, completed: true, cumulative_by_depth: vec![1, 5, 10] },
        ));
        // Equal incomplete prefix (e.g., deterministic startup exhausting depth cap): keep symmetry.
        let startup = ReducedProbe { distinct: 9, completed: false, cumulative_by_depth: vec![1, 2, 3, 4, 5, 6, 7, 8, 9] };
        assert!(!projection_beats_sym(&startup, &startup));
        // Projection completes strictly smaller than symmetry's incomplete cap: projection wins.
        assert!(projection_beats_sym(
            &ReducedProbe { distinct: 400, completed: true, cumulative_by_depth: vec![1, 50, 400] },
            &ReducedProbe { distinct: 1025, completed: false, cumulative_by_depth: vec![1, 100] },
        ));
        // Projection finishes but symmetry timed out before reaching projection's count: inconclusive, keep symmetry.
        assert!(!projection_beats_sym(
            &ReducedProbe { distinct: 400, completed: true, cumulative_by_depth: vec![1, 50, 400] },
            &ReducedProbe { distinct: 200, completed: false, cumulative_by_depth: vec![1, 100] },
        ));
        // Symmetry finishes while projection is incomplete: keep symmetry.
        assert!(!projection_beats_sym(
            &ReducedProbe { distinct: 1025, completed: false, cumulative_by_depth: vec![1, 100] },
            &ReducedProbe { distinct: 378, completed: true, cumulative_by_depth: vec![1, 20, 378] },
        ));
        // No comparable shared BFS level (e.g., symmetry timed out during Init): keep symmetry.
        assert!(!projection_beats_sym(
            &ReducedProbe { distinct: 343, completed: false, cumulative_by_depth: vec![343] },
            &ReducedProbe { distinct: 5, completed: false, cumulative_by_depth: vec![] },
        ));
        // Equal shared prefix with an extra level on projection side: keep symmetry.
        assert!(!projection_beats_sym(
            &ReducedProbe { distinct: 20, completed: false, cumulative_by_depth: vec![1, 5, 20] },
            &ReducedProbe { distinct: 5, completed: false, cumulative_by_depth: vec![1, 5] },
        ));
        // Strict win at deepest shared completed BFS level: projection wins.
        assert!(projection_beats_sym(
            &ReducedProbe { distinct: 20, completed: false, cumulative_by_depth: vec![1, 5, 20] },
            &ReducedProbe { distinct: 8, completed: false, cumulative_by_depth: vec![1, 8] },
        ));
    }
}
