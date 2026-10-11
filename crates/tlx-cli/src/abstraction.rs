//! Artifact-only verification optimization driver. Ordinary checking and its
//! verdict/reporting paths never consume an abstraction implicitly.

use std::fmt::Write as _;
use std::path::PathBuf;
use std::process::ExitCode;

use tlx_sema::{optimize, Program};

const HELP: &str = "usage: tlx abstract Spec.tla -output DIR [-config FILE] [-I DIR]...\n\
    Emit Abstract.tla, Abstract.cfg and abstraction.txt into a new directory.\n\
    Supports scalar natural counters, INIT/NEXT and state INVARIANTs.\n\
    Requires CHECK_DEADLOCK FALSE; rejects unsupported observations.\n\
    -config FILE  configuration path (default: Spec.cfg)\n\
    -output DIR   new output directory; an existing path is never overwritten\n\
    -I DIR        additional module directory (repeatable)\n\
    -h, --help    show this help\n\
    Generates a mathematical abstraction; does not check or claim safety.\n";

pub(crate) fn run() -> ExitCode {
    match generate() {
        Ok(()) => ExitCode::SUCCESS,
        Err(message) => {
            eprintln!("tlx abstract: {message}");
            ExitCode::from(2)
        }
    }
}

fn generate() -> Result<(), String> {
    let mut args = std::env::args_os().skip(2);
    let mut spec = None;
    let mut config = None;
    let mut output = None;
    let mut includes = Vec::new();
    while let Some(arg) = args.next() {
        match arg.to_str() {
            Some("-h" | "--help") => {
                print!("{HELP}");
                return Ok(());
            }
            Some("-config" | "-output" | "-I") => {
                let path = PathBuf::from(args.next().ok_or_else(|| format!("missing value for {}", arg.to_string_lossy()))?);
                match arg.to_str() {
                    Some("-config") if config.is_none() => config = Some(path),
                    Some("-output") if output.is_none() => output = Some(path),
                    Some("-I") => includes.push(path),
                    _ => return Err(format!("duplicate option {}", arg.to_string_lossy())),
                }
            }
            Some(option) if option.starts_with('-') => return Err(format!("unsupported option {option}\n{HELP}")),
            _ if spec.is_none() => spec = Some(PathBuf::from(arg)),
            _ => return Err(format!("more than one specification\n{HELP}")),
        }
    }
    let mut spec = spec.ok_or_else(|| HELP.to_string())?;
    if spec.extension().is_none() {
        spec.set_extension("tla");
    }
    let output = output.ok_or_else(|| "missing -output DIR".to_string())?;
    let config = config.unwrap_or_else(|| spec.with_extension("cfg"));
    let text = std::fs::read_to_string(&config).map_err(|e| format!("{}: {e}", config.display()))?;
    let cfg = tlx_front::cfg::parse_cfg(&text)
        .map_err(|errors| errors.iter().map(|e| format!("{}: {e}", config.display())).collect::<Vec<_>>().join("\n"))?;
    let env = crate::settings::Env::from_env()?;
    includes.extend(env.path);
    let mut program = Program::load_with_late(&spec, &includes, &env.classpath)
        .map_err(|errors| errors.iter().map(ToString::to_string).collect::<Vec<_>>().join("\n"))?;
    let mut artifact = optimize::abstract_model(&mut program, &cfg).map_err(|error| match error.span {
        Some(span) => format!("{}:{}:{}: {}", program.file(span.file).path.display(), span.line, span.col, error.message),
        None => error.message,
    })?;
    writeln!(artifact.report, "Source: {}\nConfiguration: {}", spec.display(), config.display()).unwrap();
    for (i, file) in program.files.iter().enumerate() {
        writeln!(artifact.report, "File {i}: {}", file.path.display()).unwrap();
    }
    // All semantic work finishes before creating the destination. A partial
    // I/O failure is an error, and the explanatory report is written last.
    std::fs::create_dir(&output).map_err(|e| format!("cannot create new output directory {}: {e}", output.display()))?;
    for (name, contents) in [("Abstract.tla", artifact.module), ("Abstract.cfg", artifact.config), ("abstraction.txt", artifact.report)] {
        let path = output.join(name);
        std::fs::write(&path, contents).map_err(|e| format!("{}: {e}", path.display()))?;
    }
    println!("Finite abstraction emitted to {}. Model checking has not been performed; no safety verdict is claimed.", output.display());
    Ok(())
}
