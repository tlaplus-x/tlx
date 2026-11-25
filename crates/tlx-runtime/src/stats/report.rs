//! The `-stats` report: the text and JSON renderings of what `super`
//! collected.
//!
//! `snapshot` captures everything a report needs into one immutable
//! [`Snapshot`] (phases, totals, worker times, names, the free-form sections
//! and JSON fields other modules registered); [`text`] and [`json`] are then
//! pure functions of that snapshot, each split into one writer per report
//! section (phases, memory, search work, worker utilization, timing,
//! per-predicate tables, mixed mode, trailing sections).

use std::fmt::Write as _;
use std::sync::atomic::Ordering;

use tlx_base::format::{commas, json_string, JsonNewline};

use super::{
    flush, global, json_fields, phases, sections, Local, Metric, Path, Tally, WorkerTimes, BUDGET, C, C_NAMES, MEMORY, NC, NP, NT, P_NAMES,
    SAMPLE_EVERY, T_LABELS, T_NAMES,
};

/// Every evaluation path, in `Path` order (so its position is `Path as
/// usize`).
const PATHS: [Path; NP] = [Path::Native, Path::Ir, Path::Interp, Path::Fallback, Path::Mixed];

/// Human-readable bytes.
fn bytes(b: u64) -> String {
    if b < 1 << 20 {
        format!("{:.1} KiB", b as f64 / 1024.0)
    } else {
        format!("{:.1} MiB", b as f64 / (1 << 20) as f64)
    }
}

/// Everything the renderers need, captured once after flushing the caller.
/// Active workers contribute their last published completed-unit snapshots.
/// The text and JSON reports are pure functions of it.
struct Snapshot {
    phases: Vec<(String, Metric)>,
    total: Local,
    workers: Vec<WorkerTimes>,
    names: [Vec<String>; 3],
    sample_every: u32,
    /// The free-form sections and extra JSON fields `set_section`/`set_json`
    /// registered, in order of first setting.
    sections: Vec<(String, String)>,
    json_fields: Vec<(String, String)>,
}

fn snapshot(include_json: bool) -> Snapshot {
    flush();
    let g = global();
    let mut total = g.total.clone();
    for (_, live) in &g.live {
        total.merge(live);
    }
    let workers = g.workers.clone();
    let names = [g.action_names.clone(), g.invariant_names.clone(), g.aprop_names.clone()];
    drop(g);
    Snapshot {
        phases: phases(),
        total,
        workers,
        names,
        sample_every: SAMPLE_EVERY.load(Ordering::Relaxed),
        sections: sections(),
        json_fields: if include_json { json_fields() } else { Vec::new() },
    }
}

impl Snapshot {
    /// Factor from sampled times to estimated totals.
    fn scale(&self) -> f64 {
        let (u, s) = (self.total.c[C::Units as usize], self.total.c[C::Sampled as usize]);
        if s == 0 {
            0.0
        } else {
            u as f64 / s as f64
        }
    }

    fn est(&self, ns: u64) -> f64 {
        ns as f64 * self.scale() / 1e9
    }

    /// Estimated time of everything in the units (seconds).
    fn units_time(&self) -> f64 {
        let t = &self.total;
        let preds: u64 = [&t.actions, &t.invariants, &t.aprops].iter().flat_map(|v| v.iter()).map(|x| x.ns.iter().sum::<u64>()).sum();
        self.est(t.t.iter().sum::<u64>() + preds)
    }

    /// The name of action, invariant or action property (`kind` 0, 1, 2)
    /// `i`, with its index if the name is not unique (action instances).
    fn name(&self, kind: usize, i: usize) -> String {
        let names = &self.names[kind];
        match names.get(i) {
            Some(n) if names.iter().filter(|m| *m == n).count() > 1 => format!("{n} #{i}"),
            Some(n) => n.clone(),
            None => format!("#{i}"),
        }
    }
}

fn pct(x: f64, of: f64) -> String {
    if of > 0.0 {
        format!("{:5.1}%", 100.0 * x / of)
    } else {
        "    -".into()
    }
}

/// One metric as shown in the phases and memory sections.
fn show(m: &Metric) -> String {
    match m {
        Metric::Secs(x) => format!("{x:.3}s"),
        Metric::Count(n) => commas(*n),
        Metric::Bytes(b) => bytes(*b),
        Metric::Text(t) => t.clone(),
    }
}

const KINDS: [(&str, &str); 3] = [("actions", "actions"), ("invariants", "invariants"), ("action properties", "action_properties")];

fn tallies(t: &Local) -> [&Vec<Tally>; 3] {
    [&t.actions, &t.invariants, &t.aprops]
}

// ----------------------------------------------------------------------
// text: one writer per section

impl Snapshot {
    /// The `phases:` block: every non-memory phase in record order.
    fn write_phases(&self, o: &mut String) {
        let _ = writeln!(o, "phases:");
        for (k, m) in self.phases.iter().filter(|(k, _)| !k.starts_with(MEMORY)) {
            let _ = writeln!(o, "  {k:<36} {}", show(m));
        }
    }

    /// The memory block: every `MEMORY` phase, each with its share of the
    /// budget when there is one.
    fn write_memory(&self, o: &mut String) {
        let _ = writeln!(o, "memory (peaks of the components; est. = estimated from sizes; % of the budget):");
        let budget =
            self.phases.iter().find(|(k, _)| k == BUDGET).and_then(|(_, m)| if let Metric::Bytes(b) = m { Some(*b) } else { None });
        for (k, m) in self.phases.iter().filter(|(k, _)| k.starts_with(MEMORY)) {
            let share = match (m, budget) {
                (Metric::Bytes(b), Some(t)) if k != BUDGET && t > 0 => format!(" ({:.1}%)", 100.0 * *b as f64 / t as f64),
                _ => String::new(),
            };
            let _ = writeln!(o, "  {:<36} {}{share}", &k[MEMORY.len()..], show(m));
        }
    }

    /// The `search work:` block: expanded units, successors, levels, the
    /// fingerprint set, encodings and interpreter definition evaluations.
    fn write_work(&self, o: &mut String) {
        let t = &self.total;
        let c = |x: C| t.c[x as usize];
        let units = c(C::Units);
        if units == 0 {
            return;
        }
        let _ = writeln!(o, "search work:");
        let _ = writeln!(
            o,
            "  units (states expanded, simulation steps) {} (timed: {}, 1 in {}); successors generated {}",
            commas(units),
            commas(c(C::Sampled)),
            self.sample_every,
            commas(c(C::Generated))
        );
        if c(C::Traces) > 0 {
            let _ = writeln!(o, "  behaviors generated {}", commas(c(C::Traces)));
        }
        let levels = t.levels.iter().filter(|&&n| n > 0).count();
        if let Some((d, w)) = t.levels.iter().enumerate().max_by_key(|e| *e.1) {
            let _ = writeln!(o, "  levels {levels}, widest {} at depth {d}", commas(*w));
        }
        let ins = c(C::FpInserts);
        if ins > 0 {
            let _ = writeln!(
                o,
                "  fingerprint set: {} inserts, {} new ({:.1}%), {:.3} extra probes per insert",
                commas(ins),
                commas(c(C::FpNew)),
                100.0 * c(C::FpNew) as f64 / ins as f64,
                c(C::FpProbes) as f64 / ins as f64
            );
        }
        if c(C::Encodes) + c(C::Decodes) + c(C::Fingerprints) > 0 {
            let _ = writeln!(
                o,
                "  encoded states: {} encodes, {} decodes, {} fingerprints of encodings",
                commas(c(C::Encodes)),
                commas(c(C::Decodes)),
                commas(c(C::Fingerprints))
            );
        }
        if c(C::DefEvals) + c(C::DefEvalsPrimed) > 0 {
            let _ = writeln!(
                o,
                "  state-level definitions evaluated by the interpreter: {} in a current state, {} in a next state",
                commas(c(C::DefEvals)),
                commas(c(C::DefEvalsPrimed))
            );
        }
    }

    /// The worker-utilization block: busy / waiting / barrier shares and the
    /// units of each worker run.
    fn write_utilization(&self, o: &mut String) {
        if self.workers.is_empty() {
            return;
        }
        let life: u64 = self.workers.iter().map(|w| w.life_ns).sum();
        let idle: u64 = self.workers.iter().map(|w| w.idle_ns).sum();
        let barrier: u64 = self.workers.iter().map(|w| w.barrier_ns).sum();
        let busy = life.saturating_sub(idle + barrier);
        let _ = writeln!(
            o,
            "workers ({} thread runs, {:.3} thread-seconds): busy {}, waiting for work {}, at level barriers {}",
            self.workers.len(),
            life as f64 / 1e9,
            pct(busy as f64, life as f64).trim(),
            pct(idle as f64, life as f64).trim(),
            pct(barrier as f64, life as f64).trim()
        );
        if self.workers.len() > 1 {
            let per: Vec<String> = self.workers.iter().map(|w| commas(w.units)).collect();
            let _ = writeln!(o, "  units per worker run: {}", per.join(" "));
        }
    }

    /// The timing block: estimated thread-seconds per timer and per
    /// action/invariant/action-property path, sorted by estimated time.
    fn write_timing(&self, o: &mut String) {
        if self.scale() <= 0.0 {
            return;
        }
        let t = &self.total;
        let total = self.units_time();
        let _ = writeln!(o, "time in search units (extrapolated from the timed units; thread-seconds): {total:.3}s");
        let mut rows: Vec<(String, f64)> = Vec::new();
        for (k, v) in KINDS.iter().zip(tallies(t)) {
            for (path, pname) in PATHS.iter().zip(P_NAMES) {
                let ns: u64 = v.iter().map(|x| x.ns[*path as usize]).sum();
                if ns > 0 {
                    rows.push((format!("{} ({pname})", k.0), self.est(ns)));
                }
            }
        }
        for (label, &ns) in T_LABELS.iter().zip(&t.t) {
            if ns > 0 {
                rows.push((label.to_string(), self.est(ns)));
            }
        }
        rows.sort_by(|a, b| b.1.total_cmp(&a.1));
        for (k, x) in rows {
            let _ = writeln!(o, "  {k:<36} {x:9.3}s {}", pct(x, total));
        }
    }

    /// One table per kind (actions, invariants, action properties): calls
    /// and successors by evaluation path, in name order.
    fn write_predicates(&self, o: &mut String) {
        let t = &self.total;
        let total = self.units_time();
        for (kind, (k, v)) in KINDS.iter().zip(tallies(t)).enumerate() {
            if v.iter().all(|x| x.calls.iter().sum::<u64>() == 0 && x.succs == 0) {
                continue;
            }
            let succ_head = if kind == 0 { format!(" {:>12}", "successors") } else { String::new() };
            let mixed = v.iter().any(|x| x.calls[Path::Mixed as usize] > 0);
            let mixed_head = if mixed { format!(" {:>12}", "mixed") } else { String::new() };
            let _ = writeln!(
                o,
                "{:<30} {:>12}{mixed_head} {:>12} {:>12} {:>12}{succ_head} {:>10} {:>6}",
                k.0, "native", "ir", "interp", "fallback", "est. time", "share"
            );
            for (i, x) in v.iter().enumerate() {
                if x.calls.iter().sum::<u64>() == 0 && x.succs == 0 {
                    continue;
                }
                let ns: u64 = x.ns.iter().sum();
                let mut name = self.name(kind, i);
                if name.chars().count() > 28 {
                    name = name.chars().take(27).collect::<String>() + "~";
                }
                let succ = if kind == 0 { format!(" {:>12}", commas(x.succs)) } else { String::new() };
                let col = |p: Path| commas(x.calls[p as usize]);
                let mixed_col = if mixed { format!(" {:>12}", col(Path::Mixed)) } else { String::new() };
                let _ = writeln!(
                    o,
                    "  {name:<28} {:>12}{mixed_col} {:>12} {:>12} {:>12}{succ} {:>9.3}s {}",
                    col(Path::Native),
                    col(Path::Ir),
                    col(Path::Interp),
                    col(Path::Fallback),
                    self.est(ns),
                    pct(self.est(ns), total)
                );
            }
        }
    }

    /// The mixed-mode block: what the mixed calls did in host regions and
    /// the sampled time per call of each path (to compare mixed with the
    /// fallback paths).
    fn write_mixed(&self, o: &mut String) {
        let t = &self.total;
        let mut lines = Vec::new();
        for (kind, v) in tallies(t).into_iter().enumerate() {
            for (i, x) in v.iter().enumerate() {
                let m = Path::Mixed as usize;
                if x.calls[m] == 0 {
                    continue;
                }
                let per = |p: Path| {
                    let p = p as usize;
                    if x.sampled[p] > 0 {
                        format!("{:.2}", x.ns[p] as f64 / x.sampled[p] as f64 / 1e3)
                    } else {
                        "-".into()
                    }
                };
                lines.push(format!(
                    "  {:<11} {:<28} {:>12} regions ({:.1} per mixed call), {} failed; us/call mixed {} native {} ir {} interp {} fallback {}",
                    ["action", "invariant", "action prop."][kind],
                    self.name(kind, i),
                    commas(x.regions),
                    x.regions as f64 / x.calls[m] as f64,
                    commas(x.region_errors),
                    per(Path::Mixed),
                    per(Path::Native),
                    per(Path::Ir),
                    per(Path::Interp),
                    per(Path::Fallback)
                ));
            }
        }
        if !lines.is_empty() {
            let _ = writeln!(o, "mixed-mode functions (host region evaluations; sampled time per call by path):");
            for l in lines {
                let _ = writeln!(o, "{l}");
            }
        }
    }

    /// The free-form sections other modules registered (`set_section`), in
    /// order of first setting.
    fn write_sections(&self, o: &mut String) {
        for (title, text) in &self.sections {
            let _ = writeln!(o, "{title}:");
            o.push_str(text);
        }
    }
}

/// The human-readable report of one snapshot.
fn text_of(s: &Snapshot) -> String {
    let mut o = String::new();
    let _ = writeln!(o, "==== tlx statistics (-stats) ====");
    s.write_phases(&mut o);
    s.write_memory(&mut o);
    s.write_work(&mut o);
    s.write_utilization(&mut o);
    s.write_timing(&mut o);
    s.write_predicates(&mut o);
    s.write_mixed(&mut o);
    s.write_sections(&mut o);
    o
}

/// The human-readable report.
pub fn text() -> String {
    text_of(&snapshot(false))
}

// ----------------------------------------------------------------------
// JSON

/// A JSON string literal; a line feed keeps its short `\n` spelling.
pub(crate) fn js(s: &str) -> String {
    json_string(s, JsonNewline::Short)
}

/// A JSON number.
fn jf(x: f64) -> String {
    if x.is_finite() {
        format!("{x:.6}")
    } else {
        "null".into()
    }
}

/// A JSON object from rendered `name: value` fields, in order.
fn obj(kv: Vec<(String, String)>) -> String {
    format!("{{{}}}", kv.into_iter().map(|(k, v)| format!("{}:{v}", js(&k))).collect::<Vec<_>>().join(","))
}

/// A JSON array of rendered elements.
fn jarr(items: &[String]) -> String {
    format!("[{}]", items.join(","))
}

impl Snapshot {
    /// The phases object (`memory` false) or the memory object (`memory`
    /// true), with the `MEMORY` prefix stripped from the keys.
    fn json_metrics(&self, memory: bool) -> String {
        obj(self
            .phases
            .iter()
            .filter(|(k, _)| k.starts_with(MEMORY) == memory)
            .map(|(k, m)| {
                let v = match m {
                    Metric::Secs(x) => jf(*x),
                    Metric::Count(n) | Metric::Bytes(n) => n.to_string(),
                    Metric::Text(t) => js(t),
                };
                (k.strip_prefix(MEMORY).unwrap_or(k).to_string(), v)
            })
            .collect())
    }

    /// One field per kind (actions, invariants, action properties): a JSON
    /// array of the tallies, in name order.
    fn json_tallies(&self) -> Vec<(String, String)> {
        KINDS
            .iter()
            .zip(tallies(&self.total))
            .enumerate()
            .map(|(kind, (k, v))| {
                let rows: Vec<String> = v
                    .iter()
                    .enumerate()
                    .map(|(i, x)| {
                        obj(vec![
                            ("name".to_string(), js(&self.name(kind, i))),
                            (
                                "calls".to_string(),
                                obj(PATHS.iter().zip(P_NAMES).map(|(p, n)| (n.to_string(), x.calls[*p as usize].to_string())).collect()),
                            ),
                            ("fully_native".to_string(), x.fully_native.to_string()),
                            ("successors".to_string(), x.succs.to_string()),
                            ("region_evals".to_string(), x.regions.to_string()),
                            ("region_errors".to_string(), x.region_errors.to_string()),
                            (
                                "est_s".to_string(),
                                obj(PATHS.iter().zip(P_NAMES).map(|(p, n)| (n.to_string(), jf(self.est(x.ns[*p as usize])))).collect()),
                            ),
                        ])
                    })
                    .collect();
                (k.1.to_string(), jarr(&rows))
            })
            .collect()
    }

    /// The `workers` JSON array.
    fn json_workers(&self) -> String {
        let rows: Vec<String> = self
            .workers
            .iter()
            .map(|w| {
                obj(vec![
                    ("life_s".to_string(), jf(w.life_ns as f64 / 1e9)),
                    ("idle_s".to_string(), jf(w.idle_ns as f64 / 1e9)),
                    ("barrier_s".to_string(), jf(w.barrier_ns as f64 / 1e9)),
                    ("units".to_string(), w.units.to_string()),
                ])
            })
            .collect();
        jarr(&rows)
    }
}

/// The machine-readable report of one snapshot: one JSON object.
fn json_of(s: &Snapshot) -> String {
    let t = &s.total;
    let mut fields = vec![
        ("sample_every".to_string(), s.sample_every.to_string()),
        ("phases".into(), s.json_metrics(false)),
        ("memory".into(), s.json_metrics(true)),
        ("counters".into(), obj((0..NC).map(|i| (C_NAMES[i].to_string(), t.c[i].to_string())).collect())),
        ("time_est_s".into(), obj((0..NT).map(|i| (T_NAMES[i].to_string(), jf(s.est(t.t[i])))).collect())),
        ("units_time_est_s".into(), jf(s.units_time())),
    ];
    fields.extend(s.json_tallies());
    fields.push(("levels".into(), jarr(&t.levels.iter().map(|n| n.to_string()).collect::<Vec<_>>())));
    fields.push(("workers".into(), s.json_workers()));
    fields.push(("sections".into(), obj(s.sections.iter().map(|(k, v)| (k.clone(), js(v))).collect())));
    fields.extend(s.json_fields.iter().cloned());
    obj(fields)
}

/// The machine-readable report: one JSON object.
pub fn json() -> String {
    json_of(&snapshot(true))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::stats::T;

    fn counters(list: &[(C, u64)]) -> [u64; NC] {
        let mut c = [0u64; NC];
        for &(k, v) in list {
            c[k as usize] = v;
        }
        c
    }

    fn times(list: &[(T, u64)]) -> [u64; NT] {
        let mut t = [0u64; NT];
        for &(k, v) in list {
            t[k as usize] = v;
        }
        t
    }

    #[allow(clippy::too_many_arguments)]
    fn tally(
        calls: &[(Path, u64)],
        sampled: &[(Path, u64)],
        ns: &[(Path, u64)],
        fully_native: u64,
        succs: u64,
        regions: u64,
        region_errors: u64,
    ) -> Tally {
        let mut t = Tally::default();
        for &(p, v) in calls {
            t.calls[p as usize] = v;
        }
        for &(p, v) in sampled {
            t.sampled[p as usize] = v;
        }
        for &(p, v) in ns {
            t.ns[p as usize] = v;
        }
        t.fully_native = fully_native;
        t.succs = succs;
        t.regions = regions;
        t.region_errors = region_errors;
        t
    }

    /// An empty snapshot, as when `-stats` collected nothing.
    fn empty() -> Snapshot {
        Snapshot {
            phases: Vec::new(),
            total: Local::new(),
            workers: Vec::new(),
            names: [Vec::new(), Vec::new(), Vec::new()],
            sample_every: 8,
            sections: Vec::new(),
            json_fields: Vec::new(),
        }
    }

    /// A populated snapshot: memory and non-memory phases, units, a
    /// duplicate action name, a mixed call, two workers and levels.
    fn mixed() -> Snapshot {
        let mut total = Local::new();
        total.c = counters(&[
            (C::Units, 1000),
            (C::Sampled, 125),
            (C::Generated, 3000),
            (C::FpInserts, 900),
            (C::FpNew, 850),
            (C::FpProbes, 100),
            (C::Encodes, 5),
            (C::Decodes, 5),
            (C::Fingerprints, 5),
            (C::Traces, 2),
            (C::DefEvals, 3),
            (C::DefEvalsPrimed, 2),
        ]);
        total.t = times(&[
            (T::Unit, 1_000_000),
            (T::Successor, 200_000),
            (T::FpSet, 50_000),
            (T::Invariants, 30_000),
            (T::Transition, 10_000),
            (T::Fingerprint, 5_000),
        ]);
        total.actions = vec![
            tally(
                &[(Path::Native, 100), (Path::Mixed, 10)],
                &[(Path::Native, 12), (Path::Mixed, 2)],
                &[(Path::Native, 120_000), (Path::Mixed, 20_000)],
                90,
                3_000,
                50,
                2,
            ),
            tally(&[(Path::Interp, 5)], &[(Path::Interp, 1)], &[(Path::Interp, 10_000)], 0, 0, 0, 0),
        ];
        total.invariants = vec![tally(&[(Path::Native, 100)], &[(Path::Native, 12)], &[(Path::Native, 30_000)], 100, 0, 0, 0)];
        total.aprops = vec![tally(&[(Path::Mixed, 4)], &[(Path::Mixed, 1)], &[(Path::Mixed, 4_000)], 0, 0, 8, 1)];
        total.levels = vec![10, 20, 5];
        Snapshot {
            phases: vec![
                ("front end".into(), Metric::Secs(0.123)),
                ("search".into(), Metric::Count(1234)),
                (format!("{MEMORY}frontier"), Metric::Bytes(2_000_000)),
                (BUDGET.into(), Metric::Bytes(8_000_000)),
                (format!("{MEMORY}peak RSS"), Metric::Bytes(4_000_000)),
                ("note".into(), Metric::Text("hello".into())),
            ],
            total,
            workers: vec![
                WorkerTimes { life_ns: 2_000_000_000, idle_ns: 100_000_000, barrier_ns: 50_000_000, units: 600 },
                WorkerTimes { life_ns: 2_000_000_000, idle_ns: 200_000_000, barrier_ns: 50_000_000, units: 400 },
            ],
            names: [vec!["Next".into(), "Next".into()], vec!["Inv".into()], vec!["Prop".into()]],
            sample_every: 8,
            sections: Vec::new(),
            json_fields: Vec::new(),
        }
    }

    /// An otherwise empty snapshot whose report carries the free-form
    /// sections and extra JSON fields other modules registered.
    fn with_sections() -> Snapshot {
        let mut s = empty();
        s.sections = vec![("auto symmetry".into(), "  groups: 2\n".into()), ("memo tables".into(), "  x\n".into())];
        s.json_fields = vec![("optimizations".into(), "[]".into())];
        s
    }

    const EMPTY_TEXT: &str = concat!(
        "==== tlx statistics (-stats) ====\n",
        "phases:\n",
        "memory (peaks of the components; est. = estimated from sizes; % of the budget):\n",
    );

    const EMPTY_JSON: &str = r#"{"sample_every":8,"phases":{},"memory":{},"counters":{"units":0,"sampled_units":0,"generated":0,"fp_inserts":0,"fp_new":0,"fp_probes":0,"encodes":0,"decodes":0,"fingerprints":0,"traces":0,"def_evals":0,"def_evals_primed":0},"time_est_s":{"unit":0.000000,"successor":0.000000,"constraint":0.000000,"fpset":0.000000,"invariants":0.000000,"transition":0.000000,"fingerprint":0.000000,"encode":0.000000,"decode":0.000000},"units_time_est_s":0.000000,"actions":[],"invariants":[],"action_properties":[],"levels":[],"workers":[],"sections":{}}"#;

    const MIXED_TEXT: &str = r#"==== tlx statistics (-stats) ====
phases:
  front end                            0.123s
  search                               1,234
  note                                 hello
memory (peaks of the components; est. = estimated from sizes; % of the budget):
  frontier                             1.9 MiB (25.0%)
  budget (-maxmem)                     7.6 MiB
  peak RSS                             3.8 MiB (50.0%)
search work:
  units (states expanded, simulation steps) 1,000 (timed: 125, 1 in 8); successors generated 3,000
  behaviors generated 2
  levels 3, widest 20 at depth 1
  fingerprint set: 900 inserts, 850 new (94.4%), 0.111 extra probes per insert
  encoded states: 5 encodes, 5 decodes, 5 fingerprints of encodings
  state-level definitions evaluated by the interpreter: 3 in a current state, 2 in a next state
workers (2 thread runs, 4.000 thread-seconds): busy 90.0%, waiting for work 7.5%, at level barriers 2.5%
  units per worker run: 600 400
time in search units (extrapolated from the timed units; thread-seconds): 0.012s
  explorer, per state                      0.008s  67.6%
  explorer, per successor                  0.002s  13.5%
  actions (native)                         0.001s   8.1%
  fingerprint set                          0.000s   3.4%
  invariants (native)                      0.000s   2.0%
  invariants (dispatch)                    0.000s   2.0%
  actions (mixed)                          0.000s   1.4%
  actions (interp)                         0.000s   0.7%
  action properties (dispatch)             0.000s   0.7%
  fingerprinting                           0.000s   0.3%
  action properties (mixed)                0.000s   0.3%
actions                              native        mixed           ir       interp     fallback   successors  est. time  share
  Next #0                               100           10            0            0            0        3,000     0.001s   9.5%
  Next #1                                 0            0            0            5            0            0     0.000s   0.7%
invariants                           native           ir       interp     fallback  est. time  share
  Inv                                   100            0            0            0     0.000s   2.0%
action properties                    native        mixed           ir       interp     fallback  est. time  share
  Prop                                    0            4            0            0            0     0.000s   0.3%
mixed-mode functions (host region evaluations; sampled time per call by path):
  action      Next #0                                50 regions (5.0 per mixed call), 2 failed; us/call mixed 10.00 native 10.00 ir - interp - fallback -
  action prop. Prop                                    8 regions (2.0 per mixed call), 1 failed; us/call mixed 4.00 native - ir - interp - fallback -
"#;

    const MIXED_JSON: &str = r#"{"sample_every":8,"phases":{"front end":0.123000,"search":1234,"note":"hello"},"memory":{"frontier":2000000,"budget (-maxmem)":8000000,"peak RSS":4000000},"counters":{"units":1000,"sampled_units":125,"generated":3000,"fp_inserts":900,"fp_new":850,"fp_probes":100,"encodes":5,"decodes":5,"fingerprints":5,"traces":2,"def_evals":3,"def_evals_primed":2},"time_est_s":{"unit":0.008000,"successor":0.001600,"constraint":0.000000,"fpset":0.000400,"invariants":0.000240,"transition":0.000080,"fingerprint":0.000040,"encode":0.000000,"decode":0.000000},"units_time_est_s":0.011832,"actions":[{"name":"Next #0","calls":{"native":100,"ir":0,"interp":0,"fallback":0,"mixed":10},"fully_native":90,"successors":3000,"region_evals":50,"region_errors":2,"est_s":{"native":0.000960,"ir":0.000000,"interp":0.000000,"fallback":0.000000,"mixed":0.000160}},{"name":"Next #1","calls":{"native":0,"ir":0,"interp":5,"fallback":0,"mixed":0},"fully_native":0,"successors":0,"region_evals":0,"region_errors":0,"est_s":{"native":0.000000,"ir":0.000000,"interp":0.000080,"fallback":0.000000,"mixed":0.000000}}],"invariants":[{"name":"Inv","calls":{"native":100,"ir":0,"interp":0,"fallback":0,"mixed":0},"fully_native":100,"successors":0,"region_evals":0,"region_errors":0,"est_s":{"native":0.000240,"ir":0.000000,"interp":0.000000,"fallback":0.000000,"mixed":0.000000}}],"action_properties":[{"name":"Prop","calls":{"native":0,"ir":0,"interp":0,"fallback":0,"mixed":4},"fully_native":0,"successors":0,"region_evals":8,"region_errors":1,"est_s":{"native":0.000000,"ir":0.000000,"interp":0.000000,"fallback":0.000000,"mixed":0.000032}}],"levels":[10,20,5],"workers":[{"life_s":2.000000,"idle_s":0.100000,"barrier_s":0.050000,"units":600},{"life_s":2.000000,"idle_s":0.200000,"barrier_s":0.050000,"units":400}],"sections":{}}"#;

    const SECTIONS_TEXT: &str = concat!(
        "==== tlx statistics (-stats) ====\n",
        "phases:\n",
        "memory (peaks of the components; est. = estimated from sizes; % of the budget):\n",
        "auto symmetry:\n",
        "  groups: 2\n",
        "memo tables:\n",
        "  x\n",
    );

    const SECTIONS_JSON: &str = r#"{"sample_every":8,"phases":{},"memory":{},"counters":{"units":0,"sampled_units":0,"generated":0,"fp_inserts":0,"fp_new":0,"fp_probes":0,"encodes":0,"decodes":0,"fingerprints":0,"traces":0,"def_evals":0,"def_evals_primed":0},"time_est_s":{"unit":0.000000,"successor":0.000000,"constraint":0.000000,"fpset":0.000000,"invariants":0.000000,"transition":0.000000,"fingerprint":0.000000,"encode":0.000000,"decode":0.000000},"units_time_est_s":0.000000,"actions":[],"invariants":[],"action_properties":[],"levels":[],"workers":[],"sections":{"auto symmetry":"  groups: 2\n","memo tables":"  x\n"},"optimizations":[]}"#;

    /// An empty report is just the header and the two section headers; both
    /// renderers agree on the labels, units and order of the counters and
    /// timers.
    #[test]
    fn empty_snapshot_renders_header_only() {
        assert_eq!(text_of(&empty()), EMPTY_TEXT);
        assert_eq!(json_of(&empty()), EMPTY_JSON);
    }

    /// The populated snapshot renders every text section and every JSON
    /// field, in the same order and with the same labels and units as
    /// before the report was split into writers.
    #[test]
    fn mixed_snapshot_renders_every_section() {
        assert_eq!(text_of(&mixed()), MIXED_TEXT);
        assert_eq!(json_of(&mixed()), MIXED_JSON);
    }

    /// The free-form sections other modules set are appended to the text and
    /// the extra JSON fields to the JSON object, both in registration order.
    #[test]
    fn sections_and_json_fields_are_appended() {
        assert_eq!(text_of(&with_sections()), SECTIONS_TEXT);
        assert_eq!(json_of(&with_sections()), SECTIONS_JSON);
    }

    /// Without timed units the scale factor is zero: every estimate
    /// collapses to zero and the text omits the timing block entirely (the
    /// populated snapshot, which has timed units, renders it).
    #[test]
    fn estimates_need_sampled_units() {
        let mut s = mixed();
        s.total.c[C::Sampled as usize] = 0;
        assert!(json_of(&s).contains("\"units_time_est_s\":0.000000"));
        assert!(!text_of(&s).contains("time in search units"));
        assert!(text_of(&mixed()).contains("time in search units"));
    }

    #[test]
    fn js_keeps_the_short_newline_spelling() {
        assert_eq!(js("line 1\n\"q\"\\\t"), "\"line 1\\n\\\"q\\\"\\\\\\u0009\"");
        assert_eq!(super::super::json_string("a\nb"), "\"a\\nb\"");
    }
}
