//! The command line: `Args` and `parse_args` (options and their values, as
//! `settings::help` lists them), the derived run parameters (memory budget,
//! fingerprint set, search options).

use super::*;

pub(crate) struct Args {
    pub(crate) spec: PathBuf,
    pub(crate) config: Option<PathBuf>,
    pub(crate) workers: usize,
    pub(crate) no_deadlock: bool,
    pub(crate) includes: Vec<PathBuf>,
    /// `TLX_CLASSPATH`: module directories searched after the built-in
    /// standard and community modules (TLC's classpath).
    pub(crate) classpath: Vec<PathBuf>,
    /// Report progress every 10 seconds instead of every minute.
    pub(crate) progress: bool,
    /// `-tool`: messages wrapped for tools (as TLC's `-tool`).
    pub(crate) tool: bool,
    /// `-nowarning`: no warnings.
    pub(crate) nowarning: bool,
    /// `-view`: show counterexample and `-dump` states through the `.cfg`
    /// `VIEW` (unless an `ALIAS` is configured).
    pub(crate) view: bool,
    /// `-difftrace`: show only the state fields that changed in a trace
    /// (and in `-dump dot` labels).
    pub(crate) difftrace: bool,
    /// The tier asked for (`-compile`, `-interp`; the last one given wins).
    pub(crate) tier: TierChoice,
    /// Compiled tier over encoded states (`tier`, resolved by `resolve_tier`).
    pub(crate) compile: bool,
    /// Why the default tier is the interpreter in this run (no native code
    /// possible), printed once.
    pub(crate) tier_note: Option<String>,
    /// `-tlc`: TLC-compatible results (the contract of docs/compat.md §0:
    /// verdicts, violated names, counts, depth, shortest-trace length). The
    /// default mode may use sound reductions, such as the symmetry tlx proves
    /// (`-noautosymmetry` turns that off); it keeps the verdicts and genuine
    /// counterexamples, but its counts, depth and counterexample may differ
    /// from TLC's. `-tlc` applies none of them.
    pub(crate) tlc: bool,
    /// Opt-in proven state-space reductions.
    pub(crate) optimize: bool,
    /// `-proofdir DIR` (or `TLX_PROOF_DIR`): directory for generated Lean
    /// optimization certificates (default: `$TLX_CACHE/proofs` or
    /// `~/.cache/tlx/proofs`).
    pub(crate) proofdir: Option<PathBuf>,
    /// `-noautosymmetry`: the default mode applies no symmetry of its own.
    pub(crate) noautosymmetry: bool,
    pub(crate) checksymmetry: bool,
    /// `-checksymmetry -suggest`: check the candidate sets of model values
    /// instead of the declared SYMMETRY.
    pub(crate) suggest: bool,
    pub(crate) symmetry: tlx_eval::model::symcheck::Bounds,
    /// Fingerprint set memory in MiB (`-fpmem`: MiB, or a fraction of the
    /// physical memory as TLC): a table of that fixed size. None: a table
    /// that grows within the memory budget.
    pub(crate) fpmem: Option<usize>,
    /// `-maxmem` (or `TLX_MAXMEM`): the memory budget in bytes (default:
    /// `tlx_runtime::mem::default_budget`).
    pub(crate) maxmem: Option<usize>,
    /// `-fpbits N`: the fingerprint set's shards.
    pub(crate) fpbits: u32,
    /// `-maxSetSize N`: the most elements a materialized set may have (TLC's
    /// `setBound`; default `tlx_value::limits::DEFAULT_MAX_SET_SIZE`).
    pub(crate) max_set_size: Option<i64>,
    /// `-simulate [num=N]`: the number of behaviors to generate.
    pub(crate) simulate: Option<u64>,
    /// `-generate`: simulation with random choices within actions.
    pub(crate) generate: bool,
    /// Maximum behavior length in simulation (`-depth -1`: unbounded).
    pub(crate) depth: u32,
    /// Whether `-depth` was given (it only has an effect in simulation).
    pub(crate) depth_given: bool,
    pub(crate) seed: Option<u64>,
    /// `-dump [dot[,actionlabels][,colorize]] file`.
    pub(crate) dump: Option<(PathBuf, tlx_runtime::DumpOptions)>,
    /// `-coverage N`: coverage statistics every N minutes and at the end.
    pub(crate) coverage: Option<Duration>,
    /// `-stats [json[=FILE]]`: performance statistics.
    pub(crate) stats: Option<stats::Out>,
    /// `TLX_QUEUE_COMPRESS_MB`, `TLX_SEG_BYTES` (testing): see `Options::queue`.
    pub(crate) queue: tlx_runtime::queue::Config,
    /// `TLX_QUEUE_COMPRESS_MB` was given (else the threshold follows the budget).
    pub(crate) queue_compress_given: bool,
    /// `TLX_FP_TABLE_MIN` (testing): the slots of the first table of a
    /// growing fingerprint set.
    pub(crate) fp_table_min: Option<usize>,
    /// `TLX_FP_SPILL_SLOTS` (testing): with `-spill always`, the slots of
    /// the fingerprint set's table that rotates to disk.
    pub(crate) fp_spill_slots: Option<usize>,
    /// `-spill`, `-metadir`, `-maxdisk` (and their variables): the disk
    /// layer, and the run's spill directory (created when first needed).
    pub(crate) spill_mode: Option<tlx_runtime::io::SpillMode>,
    pub(crate) spill_cfg: tlx_runtime::io::SpillConfig,
    pub(crate) spill: tlx_runtime::io::Spill,
    /// `-checkpoint MIN`: the interval between checkpoints (0: none; TLC's
    /// default is 30 minutes).
    pub(crate) checkpoint: Option<u64>,
    /// `-recover DIR`: continue the run checkpointed in metadir `DIR`.
    pub(crate) recover: Option<PathBuf>,
    /// The checkpoints of the run, if taken (see `checkpointer`).
    pub(crate) checkpointer: Option<Arc<tlx_runtime::Checkpointer>>,
}

pub(crate) fn usage() -> ! {
    eprintln!("{}\n(tlx check -h for the options)", settings::USAGE);
    std::process::exit(2)
}

/// A command line error: the message, then the usage.
pub(crate) fn bad_args(msg: &str) -> ! {
    eprintln!("tlx: {msg}");
    usage()
}

/// The value of option `opt`, parsed with `parse`.
pub(crate) fn opt_value<T>(opt: &str, v: Option<String>, parse: impl FnOnce(&str) -> Option<T>) -> T {
    match v {
        None => bad_args(&format!("{opt} needs a value")),
        Some(v) => parse(&v).unwrap_or_else(|| bad_args(&format!("invalid value of {opt}: {v:?}"))),
    }
}

/// Whole minutes converted into the interval representation before use.
fn minutes_duration(minutes: u64) -> Option<Duration> {
    Some(Duration::from_secs(minutes.checked_mul(60)?))
}

/// `-fpmem X`: X MiB, or (as TLC) the fraction X in (0,1) of the physical
/// memory.
pub(crate) fn parse_fpmem(v: &str) -> Option<usize> {
    if let Ok(mib) = v.parse::<usize>() {
        return (mib > 0).then_some(mib);
    }
    let f = v.parse::<f64>().ok().filter(|f| *f > 0.0 && *f < 1.0)?;
    Some(((physical_mib() as f64 * f) as usize).max(1))
}

/// The physical memory in MiB (`tlx_runtime::mem::physical_bytes`: the
/// machine's, or a lower control-group limit).
pub(crate) fn physical_mib() -> u64 {
    (tlx_runtime::mem::physical_bytes() >> 20) as u64
}

impl Args {
    /// How counterexample and `-dump` states are shown (`-view`,
    /// `-difftrace`).
    pub(crate) fn render_opts(&self) -> tlx_eval::model::StateRenderOpts {
        tlx_eval::model::StateRenderOpts { use_view: self.view, difftrace: self.difftrace }
    }

    /// Zero disables checkpoints, otherwise the seconds override wins over
    /// minutes (including minutes outside the duration range).
    pub(crate) fn checkpoint_interval(&self, seconds: Option<u64>) -> Option<Duration> {
        if self.checkpoint == Some(0) {
            None
        } else if let Some(seconds) = seconds {
            Some(Duration::from_secs(seconds))
        } else {
            let minutes = self.checkpoint.unwrap_or(30);
            Some(minutes_duration(minutes).unwrap_or_else(|| {
                bad_args(&format!("invalid value of -checkpoint: {:?} (minutes exceed the duration range)", minutes.to_string()))
            }))
        }
    }

    /// The memory budget (bytes).
    pub(crate) fn maxmem(&self) -> usize {
        self.maxmem.unwrap_or_else(tlx_runtime::mem::default_budget)
    }

    /// The fingerprint set: `-fpmem` MiB, fixed; by default a table that
    /// starts small and grows within the memory budget (`-maxmem`).
    pub(crate) fn fp_config(&self) -> tlx_runtime::FpConfig {
        let c = match self.fpmem {
            Some(mib) => tlx_runtime::FpConfig::fixed_mib(mib),
            None => {
                let c = tlx_runtime::FpConfig::growing_within(self.maxmem());
                let c = self.fp_spill_slots.map_or(c, |n| c.with_disk_slots(n));
                self.fp_table_min.map_or(c, |n| c.with_initial(n))
            }
        };
        c.with_bits(self.fpbits)
    }

    /// The most memory of the fingerprint set, in MiB.
    pub(crate) fn fp_mib(&self) -> usize {
        self.fp_config().limit_mib()
    }

    /// What limits the fingerprint set (reported when it is full).
    pub(crate) fn fp_mem(&self) -> FpMem {
        match self.fpmem {
            Some(mib) => FpMem::Fixed(mib),
            None => FpMem::Budget(self.maxmem() >> 20),
        }
    }

    /// The options of a model-checking search.
    pub(crate) fn options(&self, workers: usize, check_deadlock: bool) -> Options {
        let mut queue = self.queue;
        if !self.queue_compress_given {
            // Blocks of objects are a little faster to expand; compressed
            // blocks are much smaller: compress beyond a 16th of the
            // budget, at most 64 MiB.
            queue.compress_above = queue.compress_above.min(self.maxmem() / 16);
        }
        Options {
            workers,
            check_deadlock,
            fp: self.fp_config(),
            progress: Some(progress_reporter(if self.progress { PROGRESS_EVERY_SHORT } else { PROGRESS_EVERY })),
            safepoint_every: 0,
            queue,
            maxmem: self.maxmem(),
            spill: self.spill.clone(),
            checkpoint: self.checkpointer.clone(),
            coverage: false,
            coverage_report: None,
        }
    }
}

/// What limits the fingerprint set: `-fpmem` (MiB), or the memory budget
/// (`-maxmem`, MiB).
#[derive(Clone, Copy)]
pub(crate) enum FpMem {
    Fixed(usize),
    Budget(usize),
}

/// The execution tier asked for on the command line.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum TierChoice {
    /// Neither `-compile` nor `-interp`: the compiled tier, unless there can
    /// be no native code (`tlx_compile::enc::native_unavailable`).
    Default,
    /// `-compile`: the compiled tier.
    Compile,
    /// `-interp`: the interpreter.
    Interp,
}

impl Args {
    /// Decide `compile` from `tier` (after the compiled tier's settings are
    /// read).
    pub(crate) fn resolve_tier(&mut self) {
        self.compile = match self.tier {
            TierChoice::Interp => false,
            TierChoice::Compile => true,
            TierChoice::Default => {
                self.tier_note = tlx_compile::enc::native_unavailable();
                self.tier_note.is_none()
            }
        };
    }
}

pub(crate) fn parse_args() -> Args {
    let mut it = std::env::args().skip(1);
    match it.next().as_deref() {
        Some("check") => {}
        Some("-h" | "-help" | "--help" | "help") => {
            print!("{}", settings::help());
            std::process::exit(0)
        }
        _ => usage(),
    }
    let mut a = Args {
        spec: PathBuf::new(),
        config: None,
        workers: 1,
        no_deadlock: false,
        includes: Vec::new(),
        classpath: Vec::new(),
        progress: false,
        tool: false,
        nowarning: false,
        view: false,
        difftrace: false,
        tier: TierChoice::Default,
        compile: false,
        tier_note: None,
        tlc: false,
        optimize: false,
        proofdir: None,
        noautosymmetry: false,
        checksymmetry: false,
        suggest: false,
        symmetry: Default::default(),
        fpmem: None,
        maxmem: None,
        fpbits: 0,
        max_set_size: None,
        simulate: None,
        generate: false,
        depth: 100,
        depth_given: false,
        seed: None,
        dump: None,
        coverage: None,
        stats: None,
        queue: Default::default(),
        queue_compress_given: false,
        fp_table_min: None,
        fp_spill_slots: None,
        spill_mode: None,
        spill_cfg: Default::default(),
        spill: Default::default(),
        checkpoint: None,
        recover: None,
        checkpointer: None,
    };
    let mut spec = None;
    let mut dump_traces = Vec::new();
    let mut it = it.peekable();
    while let Some(x) = it.next() {
        match x.as_str() {
            "-h" | "-help" | "--help" => {
                print!("{}", settings::help());
                std::process::exit(0)
            }
            "-config" => a.config = Some(opt_value(&x, it.next(), |v| Some(PathBuf::from(v)))),
            "-workers" => {
                a.workers = opt_value(&x, it.next(), |w| {
                    if w == "auto" {
                        Some(std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1))
                    } else {
                        match w.parse::<usize>() {
                            Ok(0) => bad_args("-workers must be at least 1 (or \"auto\")"),
                            Ok(n) => Some(n),
                            Err(_) => None,
                        }
                    }
                })
            }
            // Like TLC: `-deadlock` turns deadlock checking OFF.
            "-deadlock" => a.no_deadlock = true,
            "-I" => a.includes.push(opt_value(&x, it.next(), |v| Some(PathBuf::from(v)))),
            "-progress" => a.progress = true,
            "-tool" => a.tool = true,
            "-nowarning" => a.nowarning = true,
            "-view" => a.view = true,
            "-difftrace" => a.difftrace = true,
            "-ir" => bad_args("-ir was removed; use -compile (the compiled tier, the default) or -interp (the interpreter)"),
            "-compile" => a.tier = TierChoice::Compile,
            "-interp" => a.tier = TierChoice::Interp,
            "-tlc" => a.tlc = true,
            "-optimize" => a.optimize = true,
            "-proofdir" => a.proofdir = Some(opt_value(&x, it.next(), |v| Some(PathBuf::from(v)))),
            "-noautosymmetry" => a.noautosymmetry = true,
            "-checksymmetry" => a.checksymmetry = true,
            "-suggest" => a.suggest = true,
            "-symmetrystates" => a.symmetry.states = opt_value(&x, it.next(), |v| v.parse().ok().filter(|n| *n > 0)),
            "-symmetrydepth" => a.symmetry.depth = opt_value(&x, it.next(), |v| v.parse().ok()),
            "-symmetryperms" => a.symmetry.permutations = opt_value(&x, it.next(), |v| v.parse().ok().filter(|n| *n > 0)),
            "-symmetryedges" => a.symmetry.edges = opt_value(&x, it.next(), |v| v.parse().ok().filter(|n| *n > 0)),
            "-fpmem" => a.fpmem = Some(opt_value(&x, it.next(), parse_fpmem)),
            "-maxmem" => a.maxmem = Some(opt_value(&x, it.next(), tlx_runtime::mem::parse_budget)),
            "-fpbits" => a.fpbits = opt_value(&x, it.next(), |v| v.parse().ok().filter(|b| *b <= tlx_runtime::fpset::MAX_BITS)),
            // As TLC: a positive int (in the range of an int).
            "-maxSetSize" => {
                a.max_set_size = Some(opt_value(&x, it.next(), |v| v.parse().ok().filter(|n| (1..=i32::MAX as i64).contains(n))))
            }
            // TLC options without effect in tlx (the spill directory is
            // removed at the end of a run; no trace-exploration spec).
            "-cleanup" | "-noGenerateSpecTE" => {}
            "-metadir" => a.spill_cfg.dir = Some(opt_value(&x, it.next(), |v| Some(PathBuf::from(v)))),
            "-spill" => a.spill_mode = Some(opt_value(&x, it.next(), tlx_runtime::io::SpillMode::parse)),
            "-maxdisk" => a.spill_cfg.maxdisk = Some(opt_value(&x, it.next(), tlx_runtime::io::parse_size)),
            // As TLC: minutes (a nonnegative integer; 0: no checkpoints).
            "-checkpoint" => a.checkpoint = Some(opt_value(&x, it.next(), |v| v.parse().ok())),
            "-recover" => a.recover = Some(opt_value(&x, it.next(), |v| Some(PathBuf::from(v)))),
            "-simulate" | "-generate" => {
                a.generate |= x == "-generate";
                a.simulate = Some(u64::MAX);
                // As TLC: an optional comma-separated list of key=value.
                if let Some(params) = it.next_if(|p| !p.starts_with('-') && p.contains('=')) {
                    for p in params.split(',') {
                        match p.split_once('=') {
                            Some(("num", n)) => a.simulate = Some(opt_value(&x, Some(n.to_string()), |n| n.parse().ok())),
                            _ => bad_args(&format!("unsupported {x} parameter {p:?} (tlx supports num=N)")),
                        }
                    }
                }
            }
            "-dump" => {
                let mut o = tlx_runtime::DumpOptions::default();
                let mut file = opt_value(&x, it.next(), |v| Some(v.to_string()));
                if file == "dot" || file.starts_with("dot,") {
                    for opt in file.split(',').skip(1) {
                        match opt {
                            "actionlabels" => o.action_labels = true,
                            "colorize" => o.colorize = true,
                            _ => {}
                        }
                    }
                    o.dot = true;
                    file = opt_value(&x, it.next(), |v| Some(v.to_string()));
                }
                // As TLC: the extension is added.
                let ext = if o.dot { ".dot" } else { ".dump" };
                if !file.ends_with(ext) {
                    file += ext;
                }
                a.dump = Some((file.into(), o));
            }
            "-dumpTrace" | "-dumptrace" => {
                let format = opt_value(&x, it.next(), |f| match f.to_ascii_lowercase().as_str() {
                    "json" => Some(dump_trace::Format::Json),
                    "tla" => Some(dump_trace::Format::Tla),
                    _ => None,
                });
                let file = opt_value(&x, it.next(), |v| Some(v.to_string()));
                dump_traces.push((format, file));
            }
            "-depth" => {
                a.depth_given = true;
                // As TLC: -1 is unbounded (Integer.MAX_VALUE).
                a.depth = opt_value(&x, it.next(), |d| match d.parse::<i64>().ok()? {
                    -1 => Some(i32::MAX as u32),
                    d if (0..=i32::MAX as i64).contains(&d) => Some(d as u32),
                    _ => None,
                });
            }
            "-stats" => {
                let (o, consumed) = stats::parse(it.peek());
                if consumed {
                    it.next();
                }
                a.stats = Some(o);
            }
            "-coverage" => a.coverage = Some(opt_value(&x, it.next(), |n| minutes_duration(n.parse().ok()?))),
            "-seed" => a.seed = Some(opt_value(&x, it.next(), |d| d.parse::<i64>().ok()) as u64),
            _ if x.starts_with('-') => bad_args(&format!("unknown option {x}")),
            _ if x.is_empty() || x == ".tla" => bad_args("empty spec name"),
            _ if spec.is_some() => bad_args(&format!("more than one spec: {x}")),
            _ => spec = Some(PathBuf::from(x)),
        }
    }
    if let Some((_, o)) = &mut a.dump {
        (o.use_view, o.difftrace) = (a.view, a.difftrace);
    }
    a.spec = spec.unwrap_or_else(|| bad_args("no spec given"));
    if a.spec.extension().is_none() {
        a.spec.set_extension("tla");
    }
    if a.checksymmetry && (a.simulate.is_some() || a.recover.is_some() || a.dump.is_some() || !dump_traces.is_empty()) {
        bad_args("-checksymmetry cannot be combined with simulation, recovery or state/trace dumps");
    }
    if a.suggest && !a.checksymmetry {
        bad_args("-suggest requires -checksymmetry");
    }
    dump_trace::set(dump_traces);
    a
}
