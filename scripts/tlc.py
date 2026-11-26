#!/usr/bin/env python3
"""Run TLC on a model and print its statistics as JSON; also the helpers
shared by the other scripts (running TLC, parsing TLC/tlx output).

usage: scripts/tlc.py SPEC.tla [-config X.cfg] [-workers N] [extra TLC args...]

Environment:
  TLX_JAVA   the java executable (default /opt/homebrew/opt/openjdk@21/bin/java)

Conventions shared by the scripts (see docs/configuration.md):
  -j N        parallel jobs (default DEFAULT_JOBS)
  --filter S  only corpus models whose id contains S
  --timeout S per-run timeout in seconds
  --extra=A   extra tlx arguments (write `--extra=-compile`: the value starts with '-')
"""
import tempdirs

import contextlib, json, os, re, shutil, sys, tempfile, threading

from tlxlib import ROOT, TP, CLASSPATH_DIRS, DEFAULT_JOBS, run_proc, check_tlc_model, model_cwd

JAVA = os.environ.get("TLX_JAVA", "/opt/homebrew/opt/openjdk@21/bin/java")
CLASSPATH = os.pathsep.join([os.path.join(TP, "tla2tools.jar"),
                             os.path.join(CLASSPATH_DIRS[0], "modules.jar"),
                             *CLASSPATH_DIRS[1:]])

# Sanitizer runtimes preloaded into the driver that runs the generated C
# (docs/testing.md section 11) must not reach a JVM: the JVM's own signal
# handling and alternate signal stack conflict with the Clang ASan runtime.
PRELOAD_VARS = ("LD_PRELOAD", "DYLD_INSERT_LIBRARIES")


def jvm_env(environ=None):
    """The environment of a TLC JVM launch: `environ` (default: this
    process's) without the sanitizer runtimes preloaded into the driver."""
    env = dict(os.environ if environ is None else environ)
    for name in PRELOAD_VARS:
        env.pop(name, None)
    return env


# "Temporal property P was violated." / "Temporal properties P and Q were
# violated." / "Temporal properties P, Q, and R were violated." / "Temporal
# properties were violated." (naming none). Groups: 2 = a single name,
# 3 = the "and"-joined list (possibly empty).
TEMPORAL_VIOLATED = re.compile(r"Error: Temporal propert(y (\S+) was|ies (.+ )?were) violated")


def run_tlc(spec, args, timeout=None, features=(), scratch=False, *, cwd=None, allow_local_heavy=False):
    """Run TLC on `spec` from `cwd` (default: the spec's directory); with
    `scratch`, from a copy of that directory (for specs that write files, e.g.
    CSVWrite)."""
    out, rc, wall = run_tlc_raw(spec, args, timeout, features, scratch, cwd=cwd,
                                allow_local_heavy=allow_local_heavy)
    return parse(out, wall, rc)


def run_tlc_raw(spec, args, timeout=None, features=(), scratch=False, *, cwd=None, allow_local_heavy=False):
    """Run TLC as run_tlc: its output (stdout and stderr), exit code and
    wall time. `cwd` also names the main module for TLC (relative to it)."""
    spec = os.path.abspath(spec)
    args = list(args)
    if "--allow-local-heavy" in args:
        args.remove("--allow-local-heavy")
        allow_local_heavy = True
    run_dir = cwd or os.path.dirname(spec)
    # (TLC looks the main module up relative to its working directory and the
    # `-I` directories, so a run outside the spec's own directory names it by
    # its path there - what upstream's Examples CI does from the Examples root.)
    cmd = tlc_cmd(spec, args, features, module=os.path.relpath(spec, run_dir))
    check_tlc_model(cmd, run_dir, allow_local_heavy=allow_local_heavy)
    with scratch_dir(run_dir if scratch else None) as staged:
        p = run_proc(cmd, cwd=staged or run_dir, timeout=timeout,
                     allow_local_heavy=allow_local_heavy, env=jvm_env())
    return p.stdout + p.stderr, p.returncode, p.wall


# The JVM options of every TLC run (besides the class path and -D flags).
JVM_OPTS = ["-XX:+UseParallelGC", "-Xss16m"]


def metadir():
    """TLC's -metadir (states directory) for this thread's runs (corpus.py
    runs several TLC processes at a time from its threads: each needs its
    own, or their disk queues and checkpoints collide)."""
    return os.path.join(ROOT, "target", "tlc-states", f"{os.getpid()}-{threading.get_ident()}")


def tlc_cmd(spec, args, features=(), jvm_extra=(), state_dir=None, module=None):
    """The command line of a TLC run on `spec` (run from its directory);
    `jvm_extra`: further JVM options (e.g. -D properties). `module`: the main
    module argument TLC is given, relative to the directory the run starts in
    (default: the spec's file name, for a run from the spec's own directory)."""
    flags = ["-Dtlc2.tool.impl.Tool.cdot=true"] if "action composition" in features else []
    return [JAVA, *JVM_OPTS, *flags, *jvm_extra, "-cp", CLASSPATH, "tlc2.TLC",
            "-cleanup", "-noGenerateSpecTE", "-metadir", state_dir or metadir(), *args,
            module or os.path.basename(spec)]


@contextlib.contextmanager
def scratch_dir(src):
    """A temporary copy of directory `src` (None: no directory)."""
    if src is None:
        yield None
        return
    with tempdirs.TemporaryDirectory(prefix="tlx-scratch-") as tmp:
        dst = os.path.join(tmp, os.path.basename(src))
        shutil.copytree(src, dst)
        yield dst


@contextlib.contextmanager
def model_scratch_dir(m):
    """The working directory of one run of model `m`.

    A model that writes files gets a temporary copy of its spec directory, so
    concurrent runs of one model do not collide and the shared checkout (and the
    corpus root) stays untouched; every other model runs in the directory its
    inputs are relative to (`tlxlib.model_cwd`): its own directory, or the
    corpus root for a model that names its inputs relative to that.
    """
    run_dir = model_cwd(m)  # refuses `"cwd": "root"` together with a staged copy
    if not m.get("scratch"):
        yield run_dir
        return
    with scratch_dir(run_dir) as cwd:
        yield cwd


def untool(out):
    """The plain output of a run with -tool: messages unwrapped, errors and
    warnings prefixed as without -tool."""
    prefix = {"1": "Error: ", "3": "Warning: "}
    out = re.sub(r"@!@!@STARTMSG \d+:(\d) @!@!@\n", lambda m: prefix.get(m.group(1), ""), out)
    return re.sub(r"@!@!@ENDMSG \d+ @!@!@\n", "", out)


def compile_fallback(out):
    """Whole-model fallback is a broken compiled run, even when its verdict is correct."""
    match = re.search(r"(?im)^.*compile:.*(?:IR verification failed|interpreting (?:the )?model|checking with the interpreter).*$", out)
    return match.group(0).strip() if match else None


# A failure of the machine TLC ran on, not of the model: the disk-backed state
# queue filled the filesystem (TLC's default fingerprint set spills to disk, so
# a huge model can outgrow the disk). TLC prints it as an `Error:` line, so it
# used to be parsed as a model error and stored as one in the TLC baseline store
# (2026-10-10). A killed JVM says nothing about the model either and already
# lands in the "unknown" branch below. The reason is kept as `infra`; the result
# becomes the vocabulary's existing "no usable engine output" value, which
# `contract.classify` counts as an infrastructure failure.
MACHINE_FAILURES = (
    (re.compile(r"when writing the disk \(StatePoolWriter\.run\)"), "disk full"),
    (re.compile(r"No space left on device"), "disk full"),
)


def machine_failure(out):
    """The machine failure that ended a TLC run, or None for a model outcome."""
    return next((reason for pattern, reason in MACHINE_FAILURES if pattern.search(out)), None)


def parse(out, wall, rc):
    out = untool(out)
    r = {"wall_s": round(wall, 3), "exit": rc}
    if version := re.search(r"(?m)^TLC2? Version (.+)$", out):
        r["tlc_version"] = version.group(1)
    # (The last statistics: progress reports come before.)
    if m := ([None] + list(re.finditer(r"([\d,]+) states generated, ([\d,]+) distinct states found, ([\d,]+) states left on queue", out)))[-1]:
        r["generated"], r["distinct"], r["left"] = (int(x.replace(",", "")) for x in m.groups())
    elif m := re.search(r"The number of states generated: ([\d,]+)\nSimulation using seed", out):
        r["generated"] = int(m.group(1).replace(",", ""))
    if m := re.search(r"The depth of the complete state graph search is (\d+)", out):
        r["depth"] = int(m.group(1))
    # tlx's default mode names the optimizations it applied (docs/usage.md
    # section 6.3); the counts of such a run are not TLC's, and
    # contract.compare refuses to compare them with a TLC oracle.
    if m := re.search(r"(?m)^Optimizations: (.*?)\.?$", out):
        text = m.group(1)
        r["optimizations"] = [] if text.startswith("none applicable") else [x.strip() for x in re.split(r",\s+(?![^()]*\))", text)]
    if m := re.search(r"Finished computing initial states: ([\d,]+) distinct state", out):
        r["init"] = int(m.group(1).replace(",", ""))
    if m := re.search(r"Error: Invariant (\S+|line .+? of module \S+) is violated", out):
        r["result"], r["violated"] = "safety failure", m.group(1)
    elif re.search(r"Error: Deadlock reached", out):
        r["result"] = "deadlock"
    elif m := re.search(r"Error: Action property (\S+|line .+? of module \S+) is violated", out):
        r["result"], r["violated"] = "property failure", m.group(1)
    elif m := TEMPORAL_VIOLATED.search(out):
        r["result"], r["violated"] = "liveness failure", m.group(2) or (m.group(3) or "").strip() or None
    elif m := re.search(r"Error: Property (.+) is violated by the initial state", out):
        r["result"], r["violated"] = "init property failure", m.group(1)
    elif m := re.search(r"Error: Postcondition (\S+) at .* is false", out):
        r["result"], r["violated"] = "postcondition failure", m.group(1)
    elif m := re.search(r"Error: The _POSSIBLE predicate (\S+) at .* was never witnessed", out):
        r["result"], r["violated"] = "postcondition failure", m.group(1)
    elif "Model checking completed. No error has been found." in out or ("Simulation using seed" in out and "Error:" not in out):
        r["result"] = "success"
    elif (infra := machine_failure(out)) is not None:
        # (Before the generic `Error:` branch: this `Error:` line is TLC saying
        # the machine failed, not the model. A violation found first still wins,
        # because every verdict branch above is tested first.)
        r["result"], r["infra"] = "unknown", infra
        r["error"] = out[out.index("Error:"):][:500] if "Error:" in out else out[-500:]
    elif "Error:" in out:
        r["result"] = "error"
        r["error"] = out[out.index("Error:"):][:500]
    else:
        r["result"] = "unknown"
        # (E.g. a JVM out of memory or killed: the end of the output says why.)
        r["error"] = out[-500:]
    if fallback := compile_fallback(out):
        r.update(result="compile failure", error=fallback)
    if r.get("result") in ("safety failure", "deadlock", "property failure", "init property failure"):
        states = re.findall(r"(?m)^State \d+:", out)
        if states:
            r["trace_length"] = len(states)
    return r


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print(__doc__, file=sys.stderr)
        sys.exit(2)
    print(json.dumps(run_tlc(sys.argv[1], sys.argv[2:])))
