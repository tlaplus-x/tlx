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
        && an.sets.iter().any(|s| matches!(&s.verdict, autosym::Verdict::Rejected { what, .. } if what == "CHOOSE"))
    {
        precertified = promote_certified_choices(model, &mut an);
    }
    stats::phase("auto symmetry analysis", an.elapsed);
    report(&an);
    if a.tlc {
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
        return Ok(None);
    }
    // Projection keeps priority. A group can join it only when a connected
    // certificate proves their composition for the exact installed projection.
    let projection = a.optimize.then(|| model.project_state()).flatten();
    let reusable = if projection.is_none() { precertified } else { None };
    let applied = apply(model, &mut an, a.noautosymmetry, reusable)?;
    if let Some((rule, omitted)) = projection {
        crate::proofs::emit(model, a.proofdir.as_deref(), Some((rule, &omitted)))?;
        let variables = omitted.join(", ");
        let arithmetic = match rule {
            "relative-age-projection" => "; mathematical clock arithmetic",
            "ordered-allocation-projection" => "; mathematical allocation arithmetic",
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

/// The largest group applied: the search tries every element of the group
/// on each state it finds.
const MAX_ORDER: u128 = 720;

/// The time the bounded cross-check of an applied group may take.
const CROSS_CHECK_TIME: Duration = Duration::from_millis(20);

fn eligible_proven(an: &Analysis) -> Vec<&autosym::SetResult> {
    an.proven().filter(|s| s.group_order() <= MAX_ORDER).collect()
}

struct Precertified {
    names: Vec<String>,
    group_text: String,
    certificate: String,
}

/// Apply the proven symmetry of `an` to `model` when it is allowed: the
/// safety search only (no temporal properties), no declared SYMMETRY, no
/// VIEW, and no builtin whose output or result depends on the states
/// explored. Before it is applied, a bounded check of the group runs as a
/// cross-check of the proof; a witness is an internal error (exit 101).
fn apply(model: &mut InterpModel, an: &mut Analysis, off: bool, precertified: Option<Precertified>) -> Result<Option<Applied>, ExitCode> {
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
    let reused = if forced.is_empty() {
        precertified.and_then(|pc| {
            let sel =
                pc.names.iter().map(|name| eligible.iter().copied().find(|s| s.candidate.name == *name)).collect::<Option<Vec<_>>>()?;
            Some((sel, pc.certificate))
        })
    } else {
        None
    };
    let Some((selected, certificate)) = reused.or_else(|| certify_groups(model, &eligible)) else {
        note("not applied: no connected Lean certificate for automatic symmetry");
        return Ok(None);
    };
    let gens: Vec<_> = selected.iter().flat_map(|s| s.generators()).collect();
    let text = selected.iter().filter_map(|s| s.group_text()).collect::<Vec<_>>().join(" x ");
    let bounds = Bounds { time: Some(CROSS_CHECK_TIME), ..Bounds::default() };
    let t0 = Instant::now();
    let check = symcheck::check_perms(model, gens.clone(), &bounds);
    stats::phase("auto symmetry cross-check", t0.elapsed());
    if let Ok(r) = &check {
        if let Some(w) = &r.witness {
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
    model.apply_symmetry(gens);
    model.record_symmetry_certificate(certificate);
    Ok(Some(Applied { group: text }))
}

#[derive(Clone)]
struct CandGroup<'a> {
    orig_idx: usize,
    cand: &'a autosym::SetResult,
    ord: u16,
    keys: Vec<String>,
    // Every full symmetric group of order `<= 720` (`6!`) has `2..=6` keys.
    key_ids: [u32; 6],
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
    idxs: [usize; 9],
    start: usize,
    // Every product of full symmetric groups with order `<= 720` has at most `9 * 2 = 18` keys.
    used: [u32; 24],
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
            let bucket_cap = match ord {
                720 | 120 => 1,
                24 => 2,
                6 => 3,
                _ => 9,
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

    // Best-first A* branch-and-bound ranked by admissible attainable product order (`<= 720`),
    // using binary `(take, skip)` branching so heap size stays O(pops) rather than O(N^2).
    let floor_ord = min_ord.max(2);
    let root_upper = attainable_order(1, 0, &[], full, &next_bucket);
    if root_upper < floor_ord {
        return (None, false);
    }
    let mut heap = std::collections::BinaryHeap::new();
    heap.push(SearchNode { upper: root_upper, is_leaf: false, cur_ord: 1, len: 0, idxs: [0; 9], start: 0, used: [0; 24], used_len: 0 });

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
                .filter(|ks| ks.len() <= 6)?;
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
            let mut key_ids = [0u32; 6];
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
    for s in &mut trial.sets {
        if matches!(&s.verdict, autosym::Verdict::Rejected { what, .. } if what == "CHOOSE") {
            s.verdict = autosym::Verdict::Proven { classes: vec![s.candidate.elems.clone()], pinned_by: Vec::new() };
        }
    }
    let eligible = eligible_proven(&trial);
    let (selected, certificate) = certify_groups(model, &eligible)?;
    let names: Vec<String> = selected.iter().map(|s| s.candidate.name.clone()).collect();
    let group_text = selected.iter().filter_map(|s| s.group_text()).collect::<Vec<_>>().join(" x ");
    let certified_names: std::collections::HashSet<&str> = names.iter().map(String::as_str).collect();
    for s in &mut an.sets {
        if certified_names.contains(s.candidate.name.as_str())
            && matches!(&s.verdict, autosym::Verdict::Rejected { what, .. } if what == "CHOOSE")
        {
            s.verdict = autosym::Verdict::Proven { classes: vec![s.candidate.elems.clone()], pinned_by: Vec::new() };
        }
    }
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
    if !model.symmetry_maps().is_empty() || model.ip.cfg.symmetry.is_some() {
        return Some("the cfg declares a SYMMETRY".into());
    }
    if model.has_view() && !model.has_automatic_projection() {
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

    fn mk_proven(name: &str, elems: &[&str]) -> autosym::SetResult {
        let vals: Vec<tlx_value::Value> = elems.iter().map(|s| tlx_value::Value::ModelValue(tlx_value::Sym::new(s))).collect();
        autosym::SetResult {
            candidate: autosym::Candidate { name: name.into(), elems: vals.clone() },
            verdict: autosym::Verdict::Proven { classes: vec![vals], pinned_by: Vec::new() },
        }
    }

    #[test]
    fn fallback_never_discards_higher_order_singleton_for_smaller_product() {
        // Case 1: Order-720 singleton `Big` + disjoint order-2 pair `P1 x P2` (order 4) behind
        // budget exhaustion (`U1`, `U2` fail primary `max_attempts = 2`). Must return `Big` (720)
        // immediately without probing `P1`, `P2`, or `[P1, P2]`.
        let u1 = mk_proven("U1", &["u1a", "u1b", "u1c", "u1d", "u1e", "u1f"]);
        let u2 = mk_proven("U2", &["u2a", "u2b", "u2c", "u2d", "u2e", "u2f"]);
        let big = mk_proven("Big", &["b1", "b2", "b3", "b4", "b5", "b6"]);
        let p1 = mk_proven("P1", &["p1a", "p1b"]);
        let p2 = mk_proven("P2", &["p2a", "p2b"]);
        let refs = [&u1, &u2, &big, &p1, &p2];
        let mut post_big_probed = false;
        let (sel, cert) = certify_groups_by(&refs, 16_384, 2, |gs| match gs {
            [g] if g[0] == "b1" => Some("cert-big-720".into()),
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
        assert_eq!(sel[0].candidate.name, "Big");
        assert_eq!(cert, "cert-big-720");
        assert!(!post_big_probed, "order-720 singleton must return immediately without probing smaller singletons or products");

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

        // Case 4 (R15-#3): 15 disjoint order-2 candidates (`C(15, 9) = 5,005` order-512 products)
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
}
