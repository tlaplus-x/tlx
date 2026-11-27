"""Benchmark machine, JVM and executable identity; no CLI dependencies."""
import os
import re
import sys
import subprocess

from tlxlib import ROOT, TP, git

TLX = os.path.join(ROOT, "target", "release", "tlx")


def cpu_model():
    """The CPU model name, or '' if unknown."""
    try:
        if sys.platform == "darwin":
            return subprocess.run(["sysctl", "-n", "machdep.cpu.brand_string"], capture_output=True, text=True).stdout.strip()
        out = subprocess.run(["lscpu"], capture_output=True, text=True).stdout
        names = re.findall(r"^Model name:\s*(.+)$", out, re.M)
        if names:
            return " / ".join(dict.fromkeys(n.strip() for n in names))
        with open("/proc/cpuinfo") as stream:
            return next((l.split(":", 1)[1].strip() for l in stream if l.startswith("model name")), "")
    except OSError:
        return ""


def machine_desc():
    """The machine of a benchmark: arch, CPU model, cores, TLX_BENCH_MACHINE."""
    try:
        # (Linux: the transparent huge page mode, e.g. "always [madvise] never".)
        with open("/sys/kernel/mm/transparent_hugepage/enabled") as stream:
            thp = "THP " + stream.read().strip()
    except OSError:
        thp = ""
    parts = [os.uname().machine, cpu_model(), f"{os.cpu_count()} cores", thp, os.environ.get("TLX_BENCH_MACHINE", "")]
    return ", ".join(p for p in parts if p)


def git_commit():
    c = git("rev-parse", "--short=12", "HEAD", check=False) or "unknown"
    # (The benchmark's own outputs and tooling do not change what is measured.)
    dirty = git("status", "--porcelain", "--untracked-files=no", "--", ".", ":!bench", ":!scripts/bench.py", ":!scripts/tlc.py", check=False)
    return c + ("-dirty" if dirty else "")


_FRESH = set()


def stale_source(exe):
    """A source file under crates/ newer than `exe` (None: up to date)."""
    built = os.path.getmtime(exe)
    for d, dirs, files in os.walk(os.path.join(ROOT, "crates")):
        # (Integration tests and benchmarks are not part of the binary.)
        dirs[:] = [x for x in dirs if x not in ("tests", "benches")]
        for f in files:
            if f.endswith((".rs", ".h", ".c", ".toml")) and os.path.getmtime(os.path.join(d, f)) > built:
                return os.path.relpath(os.path.join(d, f), ROOT)
    return None


def require_fresh(exe, build=None):
    """Never measure a target/release/tlx older than the sources under crates/:
    rebuild it first (2026-10-07: two cloud launches were refused in a row by
    "run cargo build --release first" after merges), and stop if it is still
    stale. Copy a binary elsewhere to measure an older build."""
    if exe in _FRESH or os.environ.get("TLX_CLOUD_HOST") == "1" or os.path.realpath(exe) != os.path.realpath(TLX):
        return
    if os.path.exists(exe) and stale_source(exe):
        print(f"{exe} is older than {stale_source(exe)}: cargo build --release", file=sys.stderr, flush=True)
        (build or (lambda: subprocess.run(["cargo", "build", "--release", "-q", "-p", "tlx"], cwd=ROOT)))()
        newer = stale_source(exe) if os.path.exists(exe) else "the binary is missing"
        if newer:
            sys.exit(f"STOP: {exe} is still older than {newer} after cargo build --release")
    _FRESH.add(exe)


def tla2tools_info():
    """Revision and version of third_party/tla2tools.jar (its manifest)."""
    import zipfile
    try:
        mf = zipfile.ZipFile(os.path.join(TP, "tla2tools.jar")).read("META-INF/MANIFEST.MF").decode()
    except (OSError, KeyError, zipfile.BadZipFile):
        return {}
    get = lambda k: (re.search(rf"^{k}: *(.*?)\s*$", mf, re.M) or [None, None])[1]
    return {"revision": get("X-Git-Revision"), "short": get("X-Git-ShortRevision"), "version": get("Implementation-Version"),
            "built": get("Build-TimeStamp")}


def sha256_short(path):
    import hashlib
    try:
        with open(path, "rb") as stream:
            return hashlib.sha256(stream.read()).hexdigest()[:16]
    except OSError:
        return None


def jvm_info():
    """The JVM's version (`java -version`) and default max heap."""
    from tlc import JAVA, JVM_OPTS
    try:
        v = subprocess.run([JAVA, "-version"], capture_output=True, text=True).stderr.strip().splitlines()
        flags = subprocess.run([JAVA, *JVM_OPTS, "-XX:+PrintFlagsFinal", "-version"], capture_output=True, text=True).stdout
    except OSError:
        return {}
    heap = re.search(r"\bMaxHeapSize\s*=\s*(\d+)", flags)
    return {"java": JAVA, "version": v, "max_heap_mib": int(heap.group(1)) >> 20 if heap else None}


def scale_workers(s, cores):
    """Worker counts from "1,16,64,max" (max: the number of CPUs), sorted."""
    return sorted({cores if x.strip() == "max" else int(x) for x in s.split(",") if x.strip()})


def mem_bytes():
    try:
        return os.sysconf("SC_PAGE_SIZE") * os.sysconf("SC_PHYS_PAGES")
    except (ValueError, OSError):
        return 0


def cpu_topology():
    """Linux (lscpu): CPUs, sockets, cores per socket, threads per core, NUMA
    nodes and their CPUs, caches; {} elsewhere."""
    try:
        out = subprocess.run(["lscpu"], capture_output=True, text=True).stdout
    except OSError:
        return {}
    return parse_lscpu(out)


LSCPU_KEYS = {"CPU(s)": "cpus", "Socket(s)": "sockets", "Core(s) per socket": "cores_per_socket", "Thread(s) per core": "threads_per_core",
              "NUMA node(s)": "numa_nodes", "Model name": "model", "L3 cache": "l3", "CPU max MHz": "max_mhz"}


def parse_lscpu(out):
    t = {}
    for line in out.splitlines():
        k, _, v = line.partition(":")
        k, v = k.strip(), v.strip()
        if k in LSCPU_KEYS:
            t.setdefault(LSCPU_KEYS[k], v)
        elif mm := re.fullmatch(r"NUMA (node\d+) CPU\(s\)", k):
            t.setdefault("numa_cpus", {})[mm.group(1)] = v
    return t


def tlc_mem_opts(frac):
    """JVM options giving TLC `frac` of the physical memory as heap and as
    direct (off-heap) memory, where TLC keeps its fingerprints (-fpmem
    stays at TLC's default, a quarter of the physical memory); [] when the
    memory is unknown or frac is 0 (the JVM's defaults, as tlcbase)."""
    gib = int(mem_bytes() * frac) >> 30
    return [f"-Xmx{gib}g", f"-XX:MaxDirectMemorySize={gib}g"] if gib > 0 else []

