//! Checkpoint identity, string-table restoration and checkpoint reporting.

use std::path::Path;
use std::process::ExitCode;
use std::sync::Arc;
use std::time::Duration;

use tlx_eval::InterpModel;

use crate::args::{bad_args, Args};
use crate::out::code;
use crate::report::EXIT_GENERAL_ERROR;
use crate::{autosym, load, out};

/// Validate recovery options and restore strings before any source is parsed.
pub(crate) fn prepare(a: &mut Args) -> Result<Option<tlx_runtime::Recovery>, ExitCode> {
    // -recover: the checkpoint's string table first (the intern order
    // decides the order of values), before anything is parsed; the run
    // goes on in its metadir (as TLC).
    match &a.recover {
        Some(dir) => {
            if a.simulate.is_some() || a.dump.is_some() {
                bad_args("-recover cannot be combined with -simulate, -generate or -dump");
            }
            match open_recovery(dir) {
                Ok(r) => {
                    a.spill_cfg.dir = Some(r.metadir().to_path_buf());
                    a.spill_cfg.reused = true;
                    Ok(Some(r))
                }
                Err(e) => {
                    out::error(code::GENERAL, &format!("cannot recover from {}: {e}", dir.display()));
                    Err(ExitCode::from(EXIT_GENERAL_ERROR))
                }
            }
        }
        None => Ok(None),
    }
}

/// Open the checkpoint of metadir `dir` and restore its string table
/// (before the spec is parsed).
fn open_recovery(dir: &Path) -> Result<tlx_runtime::Recovery, String> {
    let r = tlx_runtime::Recovery::open(dir)?;
    let strings = r.file(tlx_eval::model::STRINGS_FILE).ok_or("the checkpoint has no string table")?;
    tlx_eval::model::restore_strings(strings)?;
    Ok(r)
}

/// What a checkpoint must agree on with the run that recovers from it: the
/// tier, the mode (`-tlc` or not), the modules of the spec and the cfg (their contents), deadlock
/// checking, the seed (of constant-level random choices), and the symmetry applied without a
/// declaration (`autosym`).
pub(crate) fn run_identity(
    a: &Args,
    model: &InterpModel,
    check_deadlock: bool,
    seed: u64,
    symmetry: Option<&autosym::Applied>,
) -> Vec<(String, String)> {
    use tlx_base::frame::checksum;
    let tier = if a.compile { "-compile" } else { "the interpreter" };
    let mut spec = 0u64;
    for f in &model.ip.prog.files {
        spec = checksum(spec, f.src.as_bytes());
    }
    let cfg = std::fs::read(load::cfg_path(a)).map_or(0, |b| checksum(0, &b));
    vec![
        ("tier".into(), tier.into()),
        ("results".into(), if a.tlc { "TLC-compatible (-tlc)" } else { "the default mode" }.into()),
        ("modules".into(), format!("{} files, {spec:016x}", model.ip.prog.files.len())),
        ("configuration".into(), format!("{cfg:016x}")),
        ("deadlock".into(), if check_deadlock { "checked" } else { "not checked" }.into()),
        ("seed".into(), (seed as i64).to_string()),
        ("symmetry".into(), symmetry.map_or_else(|| "none".to_string(), |s| s.group.clone())),
        ("projection".into(), if model.has_automatic_projection() { "applied" } else { "none" }.into()),
    ]
}

/// Why checkpoint `ck` (its identity) is not of run `now`, if it is not.
pub(crate) fn identity_mismatch(ck: &[(String, String)], now: &[(String, String)]) -> Option<String> {
    for (k, v) in now {
        let old = ck.iter().find(|(k2, _)| k2 == k).map(|(_, v)| v.as_str());
        if old == Some(v.as_str()) {
            continue;
        }
        return Some(match k.as_str() {
            "tier" => format!("the checkpoint was taken with {}, this run uses {v}", old.unwrap_or("another tier")),
            "modules" => "the specification (one of its modules) changed since the checkpoint".to_string(),
            "configuration" => "the configuration changed since the checkpoint".to_string(),
            "results" => format!("the checkpoint was taken with {} results, this run asks for {v}", old.unwrap_or("other")),
            "deadlock" => format!("deadlock was {} in the checkpointed run, {v} in this one", old.unwrap_or("?")),
            _ => format!("the {k} differs (checkpoint: {}, this run: {v})", old.unwrap_or("none")),
        });
    }
    None
}

/// The checkpoints of the run: every `-checkpoint` minutes (TLC's default:
/// 30), and the testing knobs (`env`: seconds, states, abort after);
/// recovering, also to remove the checkpoint when the run ends.
pub(crate) fn checkpointer(
    checkpoint_given: bool,
    every: Option<Duration>,
    env: (Option<u64>, Option<u64>, Option<u64>),
    identity: Vec<(String, String)>,
    recovering: bool,
) -> Option<Arc<tlx_runtime::Checkpointer>> {
    let (secs, states, abort) = env;
    let off = every.is_none();
    let states = states.filter(|_| !off);
    if every.is_none() && states.is_none() && !recovering {
        return None;
    }
    let report = |e: &tlx_runtime::CheckpointEvent<'_>| match e {
        tlx_runtime::CheckpointEvent::Start(dir) => {
            out::info(code::TLC_CHECKPOINT_START, &format!("Checkpointing of run {}", dir.display()))
        }
        tlx_runtime::CheckpointEvent::Done { .. } => {
            out::info(code::TLC_CHECKPOINT_END, &format!("Checkpointing completed at ({})", out::now()))
        }
        tlx_runtime::CheckpointEvent::Failed(e) => out::warning(code::GENERAL, &format!("The checkpoint failed (the run goes on): {e}")),
    };
    Some(tlx_runtime::Checkpointer::new(tlx_runtime::CheckpointConfig {
        every,
        every_states: states,
        after: abort.map_or(tlx_runtime::AfterCommit::Continue, tlx_runtime::AfterCommit::Abort),
        identity,
        report: Some(Arc::new(report)),
        explicit: checkpoint_given || secs.is_some() || states.is_some(),
    }))
}

/// TLC's message before the search: computing the initial states, or
/// recovering from a checkpoint.
pub(crate) fn print_start(recovery: &Option<tlx_runtime::Recovery>) {
    match recovery {
        Some(r) => {
            out::info(code::TLC_CHECKPOINT_RECOVER_START, &format!("Starting recovery from checkpoint {}", r.metadir().display()));
            out::info(
                code::TLC_CHECKPOINT_RECOVER_END,
                &format!("Recovery completed. {} states examined. {} states on queue.", r.distinct(), r.queued()),
            );
        }
        None => out::info(code::TLC_COMPUTING_INIT, "Computing initial states..."),
    }
}
