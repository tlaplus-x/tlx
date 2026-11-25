"""Staging and accounting adapters shared by the benchmark entrypoints (CODE-23).

Staging a spec that writes files, resolving the measured binary, the command
and environment of a measured tlx run, and the per-child accounting of a
captured run are the same in ``bench.py``, ``bench_disk.py``,
``bench_liveness.py`` and ``bench_profile.py``; they live here so that a fix
lands once. What genuinely differs stays with its caller: the disk runner
samples its child through a control group, the liveness run wraps it in an
address-space limit, and every caller keeps its own record fields, names and
precision.

Accounting is always the child's own ``wait4`` usage, never a process-wide CPU
delta, which a concurrently reaped child of another benchmark lane would
contaminate (HARNESS-09).
"""
import contextlib
import os
import shutil
import sys

import tempdirs
from benchmarking import machine
from tlc import parse
from tlxlib import CORPUS_ROOT_CWD, mode_args as execution_args, model_cwd, tlx_env


@contextlib.contextmanager
def cache_environment(isolate=False, env=None, *, warmup=False):
    """One cache per configuration, retained across its warmup and samples."""
    run_env = dict(env or {})
    provenance = {'mode': 'inherited' if run_env.get('TLX_CACHE') or os.environ.get('TLX_CACHE') else 'shared-batch',
                  'initial_state': 'unknown', 'warmup': warmup}
    if not isolate:
        yield run_env, provenance
        return
    with tempdirs.TemporaryDirectory(prefix='tlx-bench-cache-') as cache:
        # Synchronous compilation keeps owned builds inside the cache lifetime.
        run_env.update(TLX_CACHE=cache, TLX_NATIVE_SYNC='1')
        yield run_env, {'mode': 'fresh-per-model', 'initial_state': 'empty', 'warmup': warmup}


def binary_path(path=None):
    """The absolute path of the tlx binary a measured run executes.

    Absolute because a model whose spec writes files runs with its working
    directory set to a staged copy of the spec's directory (``staged_run``),
    where a relative path would resolve to something else.
    """
    return os.path.abspath(path or machine.TLX)


def run_dir(m):
    """The directory a measured run of `m` starts in, or `None` to keep it in
    the driver's own directory (the frozen default).

    A model the corpus manifest marks `cwd: root` resolves its declared inputs
    from the corpus root (`tlxlib.model_cwd`), so its child has to start there;
    every other model keeps the documented behaviour (the driver's directory,
    with an absolute spec path, so nothing about it changes).
    """
    return model_cwd(m) if m.get("cwd") == CORPUS_ROOT_CWD else None


@contextlib.contextmanager
def staged_run(m, prefix, *, workspace=False, mode=None):
    """Yield ``(model, cwd, root)`` for one measured run in a scratch directory.

    A model whose spec writes files (``m["scratch"]``) gets its own copy of the
    spec directory per run, so concurrent runs of one model do not collide, and
    the model handed to the caller points at the copy (`cwd` is that copy, for
    the child). A model marked `cwd: root` runs in its corpus root (`run_dir`),
    where its declared inputs resolve. `workspace` makes the directory even for
    a model that writes nothing, for a caller that needs a directory of its own
    (the disk runner's state directory and its ``-stats`` file). `mode` widens
    the directory's permissions for a reader in another process (the
    control-group runner reaches it through sudo).

    `root` is None exactly when no directory was made; either way the
    directory is removed on the way out, whether the run finished, failed or
    raised.
    """
    if not (m.get("scratch") or workspace):
        yield m, run_dir(m), None
        return
    root = tempdirs.mkdtemp(prefix=prefix)
    try:
        if mode is not None:
            os.chmod(root, mode)
        model, cwd = m, run_dir(m)
        if m.get("scratch"):
            cwd = os.path.join(root, "spec")
            shutil.copytree(os.path.dirname(m["tla"]), cwd)
            shutil.copyfile(m["cfg"], os.path.join(cwd, os.path.basename(m["cfg"])))
            model = {**m, "tla": os.path.join(cwd, os.path.basename(m["tla"])),
                     "cfg": os.path.join(cwd, os.path.basename(m["cfg"]))}
        yield model, cwd, root
    finally:
        shutil.rmtree(root, ignore_errors=True)


@contextlib.contextmanager
def staged_tlc_run(m):
    """Yield ``(run_dir, module)`` for one benchmark TLC run of model `m`.

    The run starts in the directory its inputs are relative to
    (`tlxlib.model_cwd`: the spec's own directory by default, the corpus root
    for a model that names inputs relative to it) and TLC is given the main
    module relative to that directory, exactly as the correctness drivers run
    it. A model whose spec writes files still runs in a copy of its directory.
    """
    import tlc
    spec = os.path.abspath(m["tla"])
    run = tlc_run_dir(m)
    module = os.path.relpath(spec, run)
    with tlc.scratch_dir(run if m.get("scratch") else None) as staged:
        yield staged or run, module


def tlc_run_dir(m):
    """The directory one TLC run (or a TLC baseline collection) of model `m`
    starts in: the directory its inputs are relative to (`tlxlib.model_cwd`),
    or the spec's own directory when the model names no spec path."""
    return model_cwd(m) or os.path.dirname(os.path.abspath(m["tla"]))


def check_argv(binary, m, args, extra=()):
    """The command of one measured tlx run: `binary` checking model `m`.

    The execution tier comes from ``tlxlib.mode_args``, so a measured run states
    its mode explicitly instead of inheriting the binary's default; `extra`
    carries the flags of one caller's own measurement (the disk runner's
    ``-metadir`` and ``-stats``).
    """
    return [binary, "check", m["tla"], "-config", m["cfg"],
            *execution_args(binary, args, mode="default"), *extra]


def measured_env(extra=None):
    """The environment of a measured tlx child: the corpus modules' class path
    plus the caller's own overrides (an allocator switch under A/B, say)."""
    return tlx_env(classpath=True, extra=extra)


def result_of(p, timeout):
    """The parsed result of a captured child, or the deadline's own record.

    A run is a timeout when the child's own deadline expired: a child that
    failed at its own pace, and one something else killed below the deadline
    (the OOM killer), both keep their own verdict (HARNESS-09).
    """
    return {"result": "timeout", "wall_s": timeout} if p.timed_out else parse(p.stdout, p.wall, p.returncode)


def cpu_seconds(ru, *, decimals=3):
    """This child's own CPU time in seconds (user + system); `decimals` None
    keeps the exact value."""
    seconds = ru.ru_utime + ru.ru_stime
    return seconds if decimals is None else round(seconds, decimals)


def rss_mib(ru, *, decimals=1):
    """This child's peak resident memory in MiB (``ru_maxrss`` is in bytes on
    macOS and in KiB on Linux); `decimals` None keeps the exact value."""
    mib = ru.ru_maxrss / (1 << 20 if sys.platform == "darwin" else 1 << 10)
    return mib if decimals is None else round(mib, decimals)
