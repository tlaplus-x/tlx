#!/usr/bin/env python3
"""Mutation test of automatic symmetry (docs/reductions.md §6): a reduction
must never hide a violation.

For each corpus model where tlx's default mode applies a symmetry and the
state space has at most --max-states states, derive violated variants from
the unreduced state graph (`-dump` of a TLC-compatible run):

- invariant mutants `~P`, where P holds on a reachable state s: a
  conjunction, over a random subset of the variables, of "v is the value of
  v in s up to a permutation of the group" (each conjunct is closed under
  the group, so the mutant is a symmetric invariant);
- deadlock mutants: the next-state relation `Next /\\ ~Q`, Q such a
  predicate, so that the states satisfying Q have no successor.

Each mutant runs in the TLC-compatible mode (the reference) and in the
default mode, which must report the same violation (result and violated
name) with the same trace length, and for invariants the same depth. A
mutant the default mode does not report is a miss: the script exits 1.

Mutants are generated deterministically from --seed; the reference
results are cached in corpus/out/autosym-mutants.json.

Exit codes: 0 every mutant judged and detected, 1 a mutant failed (a missed
violation, a differing trace or depth, an unreduced run) or a run produced
no verdict, 2 no verdict at all (no eligible model, or not one mutant the
domain could judge - a reference that produced nothing is an infrastructure
failure, never an "invalid mutant").

usage: scripts/autosym_mutants.py [--filter S] [--ids A,B] [-j N] [--seed N]
           [--invariants N] [--deadlocks N] [--max-states N] [--timeout S]
           [--reference-args ARGS] [--default-args ARGS] [--refresh]
"""
import argparse
import tempdirs
import hashlib
import itertools
import json
import os
import random
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor

import contract
from modelcheck import structure
from tlxlib import mode_args, ROOT, DEFAULT_JOBS, build_tlx, load_oracle, run_proc, tlx_env, add_profile_args, profile_of
from tlc import parse

CACHE = os.path.join(ROOT, "corpus", "out", "autosym-mutants.json")
# The shared cfg keywords plus the two sections only this script must see:
# it re-emits the sections of a cfg it patches, while tracecheck only reads
# one (modelcheck.structure.CFG_KEYWORDS holds the common set).
CFG_KEYWORDS = structure.CFG_KEYWORDS + ("POSTCONDITIONS", "_PERIODIC")


def cfg_sections(text):
    """The sections of a cfg: [(keyword, body text)], comments removed."""
    return structure.cfg_sections(text, CFG_KEYWORDS)


def parse_states(dump):
    """The states of a `-dump` text file: [{variable: value text}]."""
    return [dict(structure.printed_pairs(block)) for block in re.split(r"(?m)^State \d+:\n", dump)[1:]]


TOKEN = re.compile(r'"(?:[^"\\]|\\.)*"|[A-Za-z_][A-Za-z0-9_]*|\s+|.')


def permute(text, perm):
    """`text` (a TLA+ value) with the model values of `perm` renamed (not in
    strings, not record field names)."""
    tokens = TOKEN.findall(text)
    out = []
    for i, t in enumerate(tokens):
        if t in perm:
            rest = "".join(tokens[i + 1:i + 8]).lstrip()
            if not rest.startswith("|->"):
                t = perm[t]
        out.append(t)
    return "".join(out)


def group_perms(classes):
    """Every permutation of the product of the full permutation groups of
    `classes` (lists of model value names), as dicts."""
    per_class = [[dict(zip(c, p)) for p in itertools.permutations(c)] for c in classes]
    for combo in itertools.product(*per_class):
        perm = {}
        for p in combo:
            perm.update({k: v for k, v in p.items() if k != v})
        yield perm


def proven_classes(suggest_out):
    """The classes of the proven groups in `-checksymmetry -suggest` output,
    and the model values of the candidate sets."""
    classes, values = [], set()
    for m in re.finditer(r"(?m)^Symmetry: (\w+) = \{([^}]*)\}: (.*)$", suggest_out):
        elems = [e.strip() for e in m.group(2).split(",") if e.strip()]
        values.update(elems)
        p = re.match(r"proven: (.*?); bounded check", m.group(3))
        if not p:
            continue
        for g in p.group(1).split(" x "):
            if g == f"Permutations({m.group(1)})":
                classes.append(elems)
            elif mm := re.fullmatch(r"Permutations\(\w+ \\ \{(.*)\}\)", g):
                out = {e.strip() for e in mm.group(1).split(",")}
                classes.append([e for e in elems if e not in out])
            elif mm := re.fullmatch(r"Permutations\(\{(.*)\}\)", g):
                classes.append([e.strip() for e in mm.group(1).split(",")])
    return classes, values


def orbit_predicate(state, names, perms, defs=None, prefix="AutosymOrb"):
    """The conjunction, over the variables `names`, of membership of the
    variable in the orbit of its value in `state`. With `defs`, each orbit
    is a 0-ary definition appended to `defs` (constant-level: TLC and tlx
    evaluate it once)."""
    conj = []
    for v in names:
        images = "{" + ", ".join(sorted({permute(state[v], p) for p in perms})) + "}"
        if defs is not None:
            name = f"{prefix}{len(defs)}"
            defs.append(f"{name} == {images}")
            images = name
        conj.append(f"{v} \\in {images}")
    return " /\\ ".join(conj)


def find_init_next(model_dir, sections):
    """The names of Init and Next of the spec `SPECIFICATION` names, from the
    definition `S == Init /\\ [][Next]_v` of a module of `model_dir` (the
    root may live in another module than the one checked); None, None when
    the model names no such spec. (tracecheck resolves the same definition
    to the formulas of Init and Next; the names are what a mutant cfg needs.)
    """

    def name(keyword):
        names = structure.cfg_names(sections, keyword)
        return names[0] if names else None

    init, nxt = name("INIT"), name("NEXT")
    if init and nxt:
        return init, nxt
    spec = name("SPECIFICATION")
    if not spec:
        return None, None
    for f in os.listdir(model_dir):
        if not f.endswith(".tla"):
            continue
        with open(os.path.join(model_dir, f), errors="replace") as stream:
            body = structure.definition(structure.strip_comments(stream.read()), spec)
        if body is None:
            continue
        if m := re.match(r"\s*(?:/\\\s*)?(\w+)\s*/\\\s*\[\]\[\s*(\w+)\s*\]_", body):
            return m.group(1), m.group(2)
    return None, None


def cfg_model_values(sections):
    """The identifiers the cfg gives as values of constants (model values)."""
    out = set()
    for k, b in sections:
        if k not in ("CONSTANT", "CONSTANTS"):
            continue
        for m in re.finditer(r"\w+\s*=\s*(\{[^}]*\}|<<[^>]*>>|\[\s*\w+\s*\]\s*\w+|\w+)", b):
            for t in TOKEN.findall(m.group(1)):
                if re.fullmatch(r"[A-Za-z_]\w*", t) and t not in ("TRUE", "FALSE"):
                    out.add(t)
    return out


def mutant_cfg(sections, *, invariant=None, init=None, nxt=None, constants=()):
    """The cfg text of a mutant: the original sections, with the invariant
    added, or Init/Next replaced (and deadlock checked)."""
    out = []
    for k, b in sections:
        if nxt and k in ("INIT", "NEXT", "SPECIFICATION", "CHECK_DEADLOCK"):
            continue
        if k in ("PROPERTY", "PROPERTIES"):
            continue
        out.append(f"{k}{b.rstrip()}\n")
    if constants:
        out.append("CONSTANTS\n" + "".join(f"  {c} = {c}\n" for c in constants))
    if invariant:
        out.append(f"INVARIANT {invariant}\n")
    if nxt:
        out.append(f"INIT {init}\nNEXT {nxt}\nCHECK_DEADLOCK TRUE\n")
    return "".join(out)


def env_args(spec):
    """Split `VAR=value ... -flag ...` into environment and arguments."""
    env, args = {}, []
    for w in shlex.split(spec):
        if re.match(r"^[A-Z_][A-Z0-9_]*=", w):
            k, v = w.split("=", 1)
            env[k] = v
        else:
            args.append(w)
    return env, args


def model_mutants(a, binary, mid, m, cache):
    """Generate and run the mutants of model `mid`; the per-mutant reports."""
    src_dir = os.path.dirname(m["tla"])
    root = os.path.splitext(os.path.basename(m["tla"]))[0]
    ref_env, ref_args = env_args(a.reference_args)
    def_env, def_args = env_args(a.default_args)
    with tempdirs.TemporaryDirectory(prefix="tlx-mutants-") as tmp:
        work = os.path.join(tmp, "model")
        shutil.copytree(src_dir, work)
        with open(m["cfg"], errors="replace") as stream:
            cfg_text = stream.read()
        flags = list(m.get("flags", []))
        p = run_proc([binary, "check", m["tla"], "-config", m["cfg"], *flags, *mode_args(binary, ["-checksymmetry", "-suggest"], mode="default")], 120,
                     cwd=work, env=tlx_env(classpath=True))
        classes, values = proven_classes(p.stdout)
        if not classes:
            return [{"model": mid, "skip": "no proven symmetry"}]
        perms = list(group_perms(classes))
        names = sorted({n for c in classes for n in c})
        if a.force_proven:
            force = sorted({mm.group(1) for mm in re.finditer(r"(?m)^Symmetry: (\w+) = .*: proven:", p.stdout)})
            def_env = {**def_env, "TLX_AUTOSYM_FORCE": ",".join(force)}
        # Does the default mode apply it?
        probe = run_proc([binary, "check", m["tla"], "-config", m["cfg"], *flags, *mode_args(binary, def_args, mode="default")], a.timeout, cwd=work,
                         env=tlx_env(classpath=True, extra=def_env))
        if "Optimizations: symmetry" not in probe.stdout:
            line = next((l for l in probe.stdout.splitlines() if l.startswith("Optimizations:")), "no Optimizations line")
            return [{"model": mid, "skip": f"not applied ({line})"}]
        dump = os.path.join(tmp, "states")
        run_proc([binary, "check", m["tla"], "-config", m["cfg"], *flags, *mode_args(binary, ref_args, mode="default"), "-dump", dump], a.timeout, cwd=work,
                 env=tlx_env(classpath=True, extra=ref_env))
        states = []
        if os.path.exists(dump + ".dump"):
            with open(dump + ".dump") as stream:
                states = parse_states(stream.read())
        if not states:
            return [{"model": mid, "skip": "no states dumped"}]
        sections = cfg_sections(cfg_text)
        init, nxt = find_init_next(work, sections)
        rng = random.Random(f"{a.seed}:{mid}")
        variables = sorted(states[0])
        defs, invariants, deadlocks, orbits = [], [], [], []
        # (Later states first: a predicate of a deep state is violated late.)
        pool = states[len(states) // 5:] or states
        # (Deadlock candidates beyond the number asked for: a state cut by
        # a CONSTRAINT loses no successors that count.)
        for k in range(a.invariants + (4 * a.deadlocks if nxt else 0)):
            s = rng.choice(pool)
            # (At least one variable that differs from the first initial
            # state, so that the predicate does not hold there.)
            moved = [v for v in variables if s[v] != states[0][v]] or variables
            first = rng.choice(moved)
            others = [v for v in variables if v != first]
            chosen = sorted([first, *rng.sample(others, min(len(others), rng.randint(0, 2)))])
            pred = orbit_predicate(s, chosen, perms, orbits)
            if k < a.invariants:
                defs.append(f"AutosymInv{k} == ~({pred})")
                invariants.append(f"AutosymInv{k}")
            else:
                defs.append(f"AutosymNext{k} == {nxt} /\\ ~({pred})")
                deadlocks.append(f"AutosymNext{k}")
        # Declare the model values the cfg mentions, except those a module
        # of the spec already declares or defines.
        declared = sorted(values | cfg_model_values(sections))
        for _ in range(len(declared) + 1):
            module = (f"---- MODULE AutosymMutants ----\nEXTENDS {root}, TLC\n"
                      + (f"CONSTANTS {', '.join(declared)}\n" if declared else "") + "\n".join(orbits + defs) + "\n====\n")
            with open(os.path.join(work, "AutosymMutants.tla"), "w") as out:
                out.write(module)
            first = invariants[0] if invariants else deadlocks[0]
            cfg_path = write_cfg(work, sections, first, init, deadlocks, declared)
            probe = run_env(binary, "AutosymMutants.tla", cfg_path, work, [*flags, *ref_args], ref_env, a.timeout)
            dup = re.search(r"Multiple declarations or definitions for symbol (\w+)|Multiply-defined symbol '(\w+)'", probe.get("out", ""))
            name = dup and (dup.group(1) or dup.group(2))
            if name not in declared:
                break
            declared.remove(name)
        reports = []
        valid_deadlocks = 0
        for kind, name in [("invariant", n) for n in invariants] + [("deadlock", n) for n in deadlocks]:
            if kind == "deadlock" and valid_deadlocks >= a.deadlocks:
                break
            cfg_path = write_cfg(work, sections, name, init, deadlocks, declared)
            with open(cfg_path) as stream:
                key = f"{mid}|{a.seed}|{name}|{hash_text(module + stream.read())}"
            ref = cache.get(key)
            if ref is None or a.refresh:
                ref = run_env(binary, "AutosymMutants.tla", cfg_path, work, [*flags, *ref_args], ref_env, a.timeout)
                ref.pop("out", None)
                ref.pop("reduced", None)
                cache[key] = ref
            got = run_env(binary, "AutosymMutants.tla", cfg_path, work, [*flags, *mode_args(binary, def_args, mode="default")], def_env, a.timeout)
            report = judge(mid, kind, name, ref, got)
            if kind == "deadlock" and report["status"] == "invalid":
                continue
            valid_deadlocks += kind == "deadlock"
            reports.append(report)
        return reports


def write_cfg(work, sections, name, init, deadlocks, declared):
    """Write the cfg of mutant `name`; its path."""
    deadlock = name in deadlocks
    cfg = mutant_cfg(sections, invariant=None if deadlock else name, init=init, nxt=name if deadlock else None, constants=declared)
    path = os.path.join(work, f"{name}.cfg")
    with open(path, "w") as out:
        out.write(cfg)
    return path


def hash_text(t):
    return hashlib.sha256(t.encode()).hexdigest()[:16]


def run_env(binary, tla, cfg, cwd, args, env, timeout):
    cmd = [binary, "check", tla, "-config", cfg, *mode_args(binary, args, mode="default")]
    try:
        p = run_proc(cmd, timeout, cwd=cwd, env=tlx_env(classpath=True, extra=env), grace=5)
    except subprocess.TimeoutExpired as e:
        return {"result": "timeout", "error": str(e)}
    except Exception as e:  # noqa: BLE001
        # (A binary that cannot be started, a missing file, a permission
        # error: the run produced nothing, which must not read as a verdict.)
        return {"result": "unknown", "error": f"{type(e).__name__}: {e}"}
    out = p.stdout + p.stderr
    return parse(out, 0, p.returncode) | {"out": out[-1500:], "reduced": "Optimizations: symmetry" in out}


def judge(mid, kind, name, ref, got):
    r = {"model": mid, "kind": kind, "mutant": name, "ref": {k: ref.get(k) for k in ("result", "violated", "trace_length", "depth")},
         "got": {k: got.get(k) for k in ("result", "violated", "trace_length", "depth")}, "reduced": got.get("reduced")}
    want = "safety failure" if kind == "invariant" else "deadlock"
    # A run that produced no result is not a judgment about the mutant: an
    # infrastructure failure of the reference (or of the reduced run) must
    # never count as a legitimate "invalid" generation outcome.
    if contract.classify(ref) != contract.OBSERVED:
        r["status"] = "infra" if contract.classify(ref) == contract.INFRA_FAILED else "timeout"
        r["note"] = f"the reference run gives {ref.get('result')}: {ref.get('error', '')}"
        r["class"] = contract.classify(ref)
        return r
    if ref.get("result") != want:
        r["status"] = "invalid"
        r["note"] = f"the reference run gives {ref.get('result')}, not {want}"
        r["class"] = contract.INCONCLUSIVE
        return r
    if contract.classify(got) != contract.OBSERVED:
        r["status"] = "infra" if contract.classify(got) == contract.INFRA_FAILED else "timeout"
        r["note"] = f"the default-mode run gives {got.get('result')}: {got.get('error', '')}"
        r["class"] = contract.classify(got)
        r["out"] = got.get("out", "")[-800:]
        return r
    r["class"] = contract.OBSERVED
    problems = []
    if got.get("result") != ref.get("result") or got.get("violated") != ref.get("violated"):
        problems.append("missed")
    elif got.get("trace_length") != ref.get("trace_length"):
        problems.append("trace length")
    elif kind == "invariant" and got.get("depth") != ref.get("depth"):
        problems.append("depth")
    if not got.get("reduced"):
        problems.append("not reduced")
    r["status"] = "ok" if not problems else ",".join(problems)
    if problems:
        r["out"] = got.get("out", "")[-800:]
    return r


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--filter", default="")
    ap.add_argument("--ids", default="")
    ap.add_argument("-j", "--jobs", dest="j", type=int, default=DEFAULT_JOBS)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--invariants", type=int, default=20)
    ap.add_argument("--deadlocks", type=int, default=5)
    ap.add_argument("--max-states", type=int, default=100_000)
    ap.add_argument("--timeout", type=int, default=120)
    ap.add_argument("--reference-args", default="-tlc", help="arguments of the TLC-compatible reference run")
    ap.add_argument("--default-args", default="", help="arguments (and VAR=value) of the default-mode run")
    ap.add_argument("--force-proven", action="store_true",
                    help="apply the proven groups through TLX_AUTOSYM_FORCE (before default mode applies them)")
    ap.add_argument("--refresh", action="store_true", help="rerun the cached reference runs")
    ap.add_argument("--report", default="", help="write the per-mutant reports to this JSON file")
    add_profile_args(ap)
    a = ap.parse_args()
    oracle = load_oracle(filter=a.filter, ids=a.ids)
    models = {k: m for k, m in oracle.items()
              if m.get("tlc", {}).get("result") == "success" and (m["tlc"].get("distinct") or 10**9) <= a.max_states}
    if not models:
        print(f"autosym_mutants: no eligible model ({len(oracle)} in the oracle, --filter {a.filter!r}, "
              f"--ids {a.ids!r}; a model needs a successful TLC oracle and at most {a.max_states} states)", file=sys.stderr)
        sys.exit(2)
    cache = {}
    if os.path.exists(CACHE):
        with open(CACHE) as stream:
            cache = json.load(stream)
    with build_tlx(profile=profile_of(a), prefix="tlx-mutants-") as binary:
        with ThreadPoolExecutor(a.j) as ex:
            results = list(ex.map(lambda kv: model_mutants(a, binary, kv[0], kv[1], cache), sorted(models.items())))
    os.makedirs(os.path.dirname(CACHE), exist_ok=True)
    with open(CACHE, "w") as output:
        json.dump(cache, output, indent=1, sort_keys=True)
    reports = [r for rs in results for r in rs]
    if a.report:
        with open(a.report, "w") as output:
            json.dump(reports, output, indent=1)
    tested = [r for r in reports if "status" in r]
    bad = [r for r in tested if r["status"] not in ("ok", "invalid")]
    for r in reports:
        if "skip" in r:
            print(f"SKIP {r['model']}: {r['skip']}")
    per_model = {}
    for r in tested:
        per_model.setdefault(r["model"], []).append(r)
    observations = contract.Observations(selected=len(tested), eligible=len(tested))
    for r in tested:
        observations.count(r.get("class", contract.OBSERVED))
    for mid, rs in sorted(per_model.items()):
        kinds = {k: sum(1 for r in rs if r["kind"] == k and r["status"] == "ok") for k in ("invariant", "deadlock")}
        invalid = sum(1 for r in rs if r["status"] == "invalid")
        lengths = sorted({r["ref"]["trace_length"] for r in rs if r["ref"].get("trace_length")})
        # (Not a single mutant this domain could judge is not a pass.)
        verdict = "FAIL" if any(r in bad for r in rs) else "PASS" if any(r["status"] == "ok" for r in rs) else "NONE"
        print(f"{verdict} {mid}: {kinds['invariant']} invariant and "
              f"{kinds['deadlock']} deadlock mutants detected, {invalid} invalid; trace lengths {lengths}")
    for r in bad:
        print(f"  {r['status']}: {r['model']} {r['mutant']} ref={r['ref']} got={r['got']}\n{r.get('out', '')}")
    print(f"{len(per_model)} models ({sum(1 for r in reports if 'skip' in r)} skipped), "
          f"{len(tested)} mutants, {len(bad)} failures")
    print(f"observations: {observations.summary()}")
    refusal = observations.refusal()
    if refusal:
        print(f"autosym_mutants: {refusal}")
    sys.exit(1 if bad else 2 if refusal else 0)


if __name__ == "__main__":
    main()
