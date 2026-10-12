//! The environment of the command line front end, read once at startup,
//! and the help text. The variables are declared in `tlx_base::knobs`
//! (the help text's environment section is generated from that table); the
//! full list of options and variables is in `docs/configuration.md`.

use std::path::PathBuf;

use tlx_base::knobs;

/// The first line of the usage message.
pub const USAGE: &str = "usage: tlx check Spec.tla [-config Spec.cfg] [-workers N|auto] [-deadlock] [-I dir]... [-progress] [-tool] [-nowarning] [-compile|-interp] [-tlc] [-optimize] [-noautosymmetry] [-checksymmetry [-suggest]] [-symmetrystates N] [-symmetrydepth D] [-symmetryperms N] [-symmetryedges N] [-maxmem MiB|fraction] [-spill auto|off|always] [-metadir DIR] [-maxdisk MiB] [-checkpoint MIN] [-recover DIR] [-fpmem MiB|fraction] [-fpbits N] [-simulate|-generate [num=N]] [-depth N] [-seed N] [-dump [dot[,actionlabels][,colorize]] file] [-dumpTrace json|tla file]... [-coverage N] [-stats [json[=FILE]]]";

/// `tlx check -h`.
const HELP_OPTIONS: &str = "\
tlx: a compiled TLA+ model checker with TLC-compatible options and output.

usage: tlx check Spec.tla [options]
       tlx parse Spec.tla   (syntax only; no module resolution or model checking)
       tlx optimize Spec.tla -output DIR [-config FILE] [-I DIR]...
                           (emit a finite optimization; see optimize -h)

Options shared with TLC (same names and meaning):
  -config FILE         the configuration file (default: Spec.cfg; a relative
                       path that does not exist is taken relative to the spec)
  -workers N|auto      number of worker threads (default 1; auto: one per core)
  -deadlock            do NOT check for deadlock (overrides CHECK_DEADLOCK)
  -simulate [num=N]    random simulation instead of model checking; N
                       behaviors per worker (default: unbounded)
  -generate [num=N]    simulation that also makes random choices within
                       actions (TLC's -generate)
  -depth N             maximum behavior length in simulation (default 100;
                       -1: unbounded)
  -seed N              seed of the simulation (default: random)
  -dump [dot[,actionlabels][,colorize]] FILE
                       write the reachable states to FILE.dump, or the state
                       graph to FILE.dot
  -dumpTrace json|tla FILE
                       after a violation (invariant, action property,
                       deadlock, temporal property), write the
                       counterexample to FILE as TLC does (JSON, or a TLA+
                       module defining CounterExample); may be repeated
  -coverage N          print TLC's coverage statistics of the actions every
                       N minutes and at the end (model checking only)
  -fpmem X             fingerprint-set memory: a fraction in (0,1) of the
                       physical memory (as TLC), or MiB if X >= 1; a table
                       of that fixed size (default: a table that starts at
                       8 MiB and grows within the -maxmem budget)
  -fpbits N            the fingerprint set's shards: 2^N ranges of high
                       fingerprint bits (0 to 30, default 0)
  -tool                wrap messages in TLC's -tool message delimiters
  -nowarning           do not print warnings
  -metadir DIR         the directory of the spill files (default: a new
                       directory states/<time> next to the spec, made only
                       when tlx first spills, removed at the end)
  -checkpoint MIN       write a checkpoint into the metadir every MIN
                       minutes (default 30, as TLC; 0: never), at the end of
                       a level of the search; it is removed when the run
                       ends, kept when the run is killed or interrupted
  -recover DIR         continue the run whose checkpoint is in metadir DIR
                       (same spec, configuration, mode and tlx binary; any
                       number of workers): same results, counts and depth
                       as an uninterrupted run; DIR is the run's metadir
  -cleanup, -noGenerateSpecTE
                       accepted for compatibility; no effect (tlx writes no
                       trace-exploration spec)

tlx options:
  -checksymmetry       check declared SYMMETRY on an unreduced bounded BFS
                       (single interpreter worker, whatever the tier);
                       exit 0: no violation within bounds, 1: witness,
                       2: incomplete or invalid diagnostic (earlier model
                       loading/assumption errors retain their normal codes)
  -suggest             with -checksymmetry: check the sets of model values
                       the cfg binds to constants instead (static proof,
                       then a bounded check; exit 101 if a proven set has
                       a witness) and print a SYMMETRY definition
  -symmetrystates N    at most N states in the symmetry BFS (default 1000)
  -symmetrydepth D     maximum transitions from Init (default 10)
  -symmetryperms N     maximum generators/fallback elements (default 100)
  -symmetryedges N     maximum successors per compared state (default 10000)
  -maxmem X            the memory budget of the search: a fraction in (0,1)
                       of the physical memory, or MiB (or with a suffix
                       K/M/G/T); default 0.5. Over budget tlx drops the
                       states kept for resuming after a layout miss,
                       writes the trace logs and then the liveness edges
                       to disk, compresses the queue of states (then
                       writes it to disk), then writes the fingerprint set
                       to disk (with -spill off: stops growing it)
                       (TLX_MAXMEM: the same)
  -spill auto|off|always
                       when tlx may write to disk: under memory pressure
                       (auto, the default), never, or always (testing: from
                       the start) (TLX_SPILL: the same)
  -maxdisk X           the most disk the spill files may take: MiB, or with
                       a suffix K/M/G/T (default: no limit; tlx always
                       leaves min(1 GiB, 2%) of the file system free)
  -I DIR               add a directory to the module search path (repeatable)
  -progress            report progress every 10 s instead of every minute
  -compile             check with the compiled tier (the default): encoded
                       states and native code (a JIT first, then C built in
                       the background and cached); same results as the
                       interpreter. Without a JIT and a C compiler the
                       default is the interpreter
  -interp              check with the interpreter (tlx's semantic
                       reference) instead; the last of -compile and
                       -interp wins
  -tlc                 TLC-compatible results: verdicts, violated names,
                       state counts, depth and shortest-trace length as
                       TLC's (docs/compat.md). The default mode may use
                       optimizations TLC does not have (it reports a
                       violation exactly when there is one, with a genuine
                       counterexample, but counts may differ): it applies
                       a symmetry of sets of model values that tlx proves
                       (safety checks only; the Optimizations line names
                       it)
  -optimize            apply proven state reductions; emit Lean, never run it (disabled by -tlc)
  -noautosymmetry      apply no symmetry tlx proves (default mode)
  -stats [json[=FILE]] report where the time and work went (phases, search
                       work, worker utilization, native/IR/interpreter runs
                       per action and predicate) on stderr when tlx exits;
                       as one JSON object with `json` (in FILE if given)
  -h, -help, --help    print this help

";

/// `tlx check -h`: the options above, then the environment variables from
/// the declaration table (`tlx_base::knobs`).
pub fn help() -> String {
    format!("{HELP_OPTIONS}{}", knobs::help_text())
}

/// The front end's environment.
pub struct Env {
    /// `TLX_PATH`: module directories searched after the `-I` ones.
    pub path: Vec<PathBuf>,
    /// `TLX_CLASSPATH`: module directories searched after the built-in
    /// standard and community modules (TLC's classpath).
    pub classpath: Vec<PathBuf>,
    /// `TLX_QUEUE_COMPRESS_MB`, `TLX_SEG_BYTES` (testing):
    /// `tlx_runtime::Options::queue`.
    pub queue: tlx_runtime::queue::Config,
    /// `TLX_QUEUE_COMPRESS_MB` was given.
    pub queue_compress_given: bool,
    /// `TLX_MAXMEM`: the memory budget (bytes), as `-maxmem`.
    pub maxmem: Option<usize>,
    /// `TLX_FP_TABLE_MIN` (testing): the slots of the first table of a
    /// growing fingerprint set.
    pub fp_table_min: Option<usize>,
    /// `TLX_FP_SPILL_SLOTS` (testing): with `-spill always`, the slots of
    /// the fingerprint set's table that rotates to disk.
    pub fp_spill_slots: Option<usize>,
    /// `TLX_SPILL`, `TLX_METADIR`, `TLX_MAXDISK`: as `-spill`, `-metadir`,
    /// `-maxdisk`.
    pub spill: Option<tlx_runtime::io::SpillMode>,
    pub metadir: Option<PathBuf>,
    pub maxdisk: Option<u64>,
    /// `TLX_CHECKPOINT_SECS`, `TLX_CHECKPOINT_STATES`, `TLX_CHECKPOINT_ABORT`
    /// (testing): checkpoints every that many seconds, or new distinct
    /// states; abort the process after the n-th one.
    pub checkpoint_secs: Option<u64>,
    pub checkpoint_states: Option<u64>,
    pub checkpoint_abort: Option<u64>,
    /// `TLX_THP`: transparent huge pages on (true), off (false) or chosen
    /// by the budget (None).
    pub thp: Option<bool>,
}

impl Env {
    /// Read the front end's variables (declared in `tlx_base::knobs`) and
    /// validate those of the compiled tier (`tlx_compile::settings`) and
    /// every other number or choice a product crate reads, so that an
    /// invalid value is reported before the check starts.
    pub fn from_env() -> Result<Env, String> {
        tlx_compile::settings::Settings::init()?;
        let env = knobs::Env::process();
        env.validate()?;
        let mut queue = tlx_runtime::queue::Config::default();
        let queue_compress = env.opt_num("TLX_QUEUE_COMPRESS_MB")?;
        if let Some(mb) = queue_compress {
            queue.compress_above = (mb as usize) << 20;
        }
        if let Some(n) = env.opt_num("TLX_SEG_BYTES")? {
            queue.seg_bytes = n as usize;
        }
        Ok(Env {
            path: env.paths("TLX_PATH"),
            classpath: env.paths("TLX_CLASSPATH"),
            queue,
            queue_compress_given: queue_compress.is_some(),
            maxmem: env.parsed("TLX_MAXMEM", tlx_runtime::mem::parse_budget)?,
            fp_table_min: env.opt_num("TLX_FP_TABLE_MIN")?.map(|n| n as usize),
            fp_spill_slots: env.opt_num("TLX_FP_SPILL_SLOTS")?.map(|n| n as usize),
            spill: env.parsed("TLX_SPILL", tlx_runtime::io::SpillMode::parse)?,
            metadir: env.path("TLX_METADIR"),
            maxdisk: env.parsed("TLX_MAXDISK", tlx_runtime::io::parse_size)?,
            checkpoint_secs: env.opt_num("TLX_CHECKPOINT_SECS")?,
            checkpoint_states: env.opt_num("TLX_CHECKPOINT_STATES")?.filter(|&n| n > 0),
            checkpoint_abort: env.opt_num("TLX_CHECKPOINT_ABORT")?.filter(|&n| n > 0),
            thp: match env.choice("TLX_THP")? {
                Some("on") => Some(true),
                Some("off") => Some(false),
                _ => None,
            },
        })
    }
}
