//! Persist the mandatory Lean output before an optimized search starts.
//! This module never invokes Lean or another verification process.

use std::io;
use std::path::PathBuf;

use tlx_eval::model::InterpModel;

use crate::out::{self, code};

pub(crate) fn emit(model: &InterpModel, applied: Option<(&str, &[String])>) -> Result<(), std::process::ExitCode> {
    let (rule, fields) = applied.map_or((None, &[][..]), |(rule, fields)| (Some(rule), fields));
    let contents =
        tlx_sema::optimize::projection_lean(&model.ip.prog, &model.ip.cfg, rule, fields, model.view_expr(), model.projection_certificate());
    let path = write(&contents).map_err(|e| {
        out::error(code::GENERAL, &format!("Cannot write mandatory optimization Lean output: {e}"));
        std::process::ExitCode::from(2)
    })?;
    let coverage = if model.projection_certificate().is_some() {
        "parametric history rule-IR certificate; lowering and runtime remain trusted"
    } else {
        "rule algebra only, model applicability remains Rust-checked"
    };
    out::info(code::GENERAL, &format!("Lean output: {} (not verified; {coverage}).", path.display()));
    Ok(())
}

fn write(contents: &str) -> io::Result<PathBuf> {
    let base = std::env::current_dir()?.join(".tlx-proofs");
    std::fs::create_dir_all(&base)?;
    // Reserve a new directory atomically. Repeated runs and concurrent CLI
    // processes never overwrite previous proofs, including after PID reuse.
    for i in 0..10_000 {
        let dir = base.join(format!("run-{}-{i}", std::process::id()));
        match std::fs::create_dir(&dir) {
            Ok(()) => {
                let path = dir.join("Optimization.lean");
                std::fs::write(&path, contents)?;
                return Ok(path);
            }
            Err(e) if e.kind() == io::ErrorKind::AlreadyExists => continue,
            Err(e) => return Err(e),
        }
    }
    Err(io::Error::new(io::ErrorKind::AlreadyExists, "cannot reserve a fresh Lean output directory"))
}
