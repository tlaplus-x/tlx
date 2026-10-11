//! Bind the command line to a model: locate and read the configuration file
//! (`-config`, `Spec.cfg`, or the `---- CONFIG Name ----` section of a `.tla`
//! file), parse the specification and the configuration, and build the
//! interpreted model, printing TLC's error messages and exit codes.

use std::path::{Path, PathBuf};
use std::process::ExitCode;

use tlx_eval::{Interp, InterpModel};
use tlx_sema::Program;

use crate::args::Args;
use crate::out;
use crate::out::code;
use crate::report::{EXIT_CONFIG_ERROR, EXIT_LIVENESS_EVAL, EXIT_SAFETY_EVAL, EXIT_SETUP_ERROR};
use crate::{cfg_name_error, cfg_subst_error};

/// The cfg file: `-config` or `Spec.cfg`; a relative path that does not
/// exist is taken relative to the spec's directory. A `-config` name
/// without the `.cfg` or `.tla` extension that does not exist as given gets
/// `.cfg` (TLC always appends it).
pub(crate) fn cfg_path(a: &Args) -> PathBuf {
    let p = a.config.clone().unwrap_or_else(|| a.spec.with_extension("cfg"));
    let in_spec_dir =
        |p: &Path| if p.is_relative() && !p.exists() { a.spec.parent().unwrap_or(Path::new(".")).join(p) } else { p.to_path_buf() };
    let found = in_spec_dir(&p);
    let known = matches!(p.extension().and_then(|e| e.to_str()), Some("cfg" | "tla"));
    if !found.exists() && !known {
        let mut with_ext = p.into_os_string();
        with_ext.push(".cfg");
        return in_spec_dir(Path::new(&with_ext));
    }
    found
}

/// The text of the configuration at `path`: the file, or the
/// `---- CONFIG Name ----` section of a `.tla` file (TLC's
/// MonolithSpecExtractor; Name is the file name without `.tla`).
fn cfg_text(path: &Path) -> std::io::Result<String> {
    let text = std::fs::read_to_string(path)?;
    match (path.extension().and_then(|e| e.to_str()), path.file_stem().and_then(|n| n.to_str())) {
        (Some("tla"), Some(name)) => Ok(tlx_front::cfg::config_section(&text, name)),
        _ => Ok(text),
    }
}

/// Parse the spec and the cfg and set up the interpreted model, printing
/// errors TLC-style.
pub(crate) fn load_model(a: &mut Args, seed: u64) -> Result<InterpModel, ExitCode> {
    let includes = a.includes.clone();
    let classpath = a.classpath.clone();
    let cfg_path = cfg_path(a);
    let mut prog = Program::load_with_late(&a.spec, &includes, &classpath).map_err(|es| {
        for e in es {
            eprintln!("{e}");
        }
        out::error(code::GENERAL, "Parsing or semantic analysis failed.");
        ExitCode::from(EXIT_SETUP_ERROR)
    })?;
    let cfg_text = cfg_text(&cfg_path).map_err(|e| {
        out::error(code::GENERAL, &format!("cannot read {}: {e}", cfg_path.display()));
        ExitCode::from(EXIT_SETUP_ERROR)
    })?;
    let cfg = tlx_front::cfg::parse_cfg(&cfg_text).map_err(|es| {
        for e in es {
            eprintln!("{}: {e}", cfg_path.display());
        }
        out::error(code::GENERAL, "Parsing the configuration failed.");
        ExitCode::from(EXIT_SETUP_ERROR)
    })?;
    // TLC (SpecProcessor.processConfig): a constant the configuration does not
    // assign is an error before anything is checked, even if it is never used
    // (EC.TLC_CONFIG_VALUE_NOT_ASSIGNED_TO_CONSTANT_PARAM, exit 151).
    if let Some(name) = prog.check_cfg_constants(&cfg) {
        out::error(
            code::TLC_CONFIG_VALUE_NOT_ASSIGNED_TO_CONSTANT_PARAM,
            &format!("The constant parameter {name} is not assigned a value by the configuration file."),
        );
        return Err(ExitCode::from(EXIT_CONFIG_ERROR));
    }
    // TLC applies the `<-` substitutions next (SpecProcessor.processSpec): a
    // side that names nothing, a mismatch of arguments or a substituted-for
    // right-hand side is a configuration error (exit 151).
    if let Some(e) = prog.check_cfg_substitutions(&cfg) {
        let (c, text) = cfg_subst_error(&e);
        out::error(c, &text);
        return Err(ExitCode::from(EXIT_CONFIG_ERROR));
    }
    // Then the names the sections refer to (SpecProcessor.processConfig)...
    if let Some(e) = prog.check_cfg_defs(&cfg) {
        let (c, text) = cfg_name_error(&e);
        out::error(c, &text);
        return Err(ExitCode::from(EXIT_CONFIG_ERROR));
    }
    if let Some(e) = prog.check_cfg_levels(&cfg) {
        println!("Error: {}", e.message());
        let code = match e {
            tlx_sema::CfgLevelError::Invariant(_) => EXIT_SAFETY_EVAL,
            tlx_sema::CfgLevelError::Property(_) => EXIT_CONFIG_ERROR,
        };
        return Err(ExitCode::from(code));
    }
    // ... and, last, whether the configuration says how to start and step
    // (SpecProcessor.processConfig; EC.TLC_CONFIG_MISSING_INIT/NEXT).
    if cfg.specification.is_none() {
        let invariants = !cfg.invariants.is_empty();
        let properties = !cfg.properties.is_empty();
        if cfg.init.is_none() && (invariants || properties || !prog.vars.is_empty()) {
            out::error(code::TLC_CONFIG_MISSING_INIT, "The configuration file did not specify the initial state predicate.");
            return Err(ExitCode::from(EXIT_CONFIG_ERROR));
        }
        if cfg.next.is_none() && (invariants || properties) {
            out::error(code::TLC_CONFIG_MISSING_NEXT, "The configuration file did not specify the next state predicate.");
            return Err(ExitCode::from(EXIT_CONFIG_ERROR));
        }
    }
    if a.optimize && a.tlc {
        out::info(code::GENERAL, "Rule-based optimization disabled by -tlc.");
    }
    // (The seed is set first: building the model may evaluate constant
    // definitions, which TLC evaluates at startup with the seeded stream.)
    let ip = Interp::new(prog, cfg).inspect(|ip| ip.set_seed(seed));
    if let Ok(ip) = &ip {
        if let Err((c, d, msg)) = ip.check_constant_substitutions() {
            out::error(
                code::TLC_CONFIG_SUBSTITUTION_NON_CONSTANT,
                &format!("The configuration file substitutes constant {c} with non-constant {d} - specifically: {msg}"),
            );
            return Err(ExitCode::from(EXIT_CONFIG_ERROR));
        }
    }
    let mut model = ip.and_then(if a.checksymmetry { InterpModel::new_unreduced } else { InterpModel::new }).map_err(|e| {
        // (A PROPERTY quantified over an empty set: SpecProcessor fails.)
        if e.message == tlx_eval::model::TAUTOLOGY {
            out::error(code::TLC_LIVE_FORMULA_TAUTOLOGY, &e.message);
            return ExitCode::from(EXIT_LIVENESS_EVAL);
        }
        out::error(code::GENERAL, &e.message);
        ExitCode::from(EXIT_SETUP_ERROR)
    })?;
    // The initial predicate of a SPECIFICATION (SpecProcessor): without one
    // (its conjuncts were definitions valued TRUE), TLC requires that there
    // is nothing to check but the assumptions, and then finds no states.
    match model.spec_init() {
        tlx_eval::model::SpecInit::Some => {}
        tlx_eval::model::SpecInit::TriviallyFalse(name) => {
            out::error(code::TLC_CONFIG_SPEC_IS_TRIVIAL, &format!("The spec is trivially false because {name} is false."));
            return Err(ExitCode::from(EXIT_CONFIG_ERROR));
        }
        tlx_eval::model::SpecInit::Empty if model.checks_states() => {
            out::error(code::TLC_CONFIG_MISSING_INIT, "The configuration file did not specify the initial state predicate.");
            return Err(ExitCode::from(EXIT_CONFIG_ERROR));
        }
        tlx_eval::model::SpecInit::Empty => model.has_behavior = false,
    }
    Ok(model)
}
