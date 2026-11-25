"""Benchmark model resolution, tier selection and stable ordering."""
import os
import re
import sys
import shutil

from tlxlib import ROOT, TP, EXTERNAL_PREFIX, load_oracle, local_path

DEFAULT = [
    "TeachingConcurrency/SimpleRegular",
    "cf1s-folklore/cf1s_folklore",
    "Bakery-Boulangerie/MCBakery",
    "btree/MCbtree",
    "lamport_mutex/MCLamportMutex",
    "transaction_commit/PaxosCommit",
    "PaxosHowToWinATuringAward/MCPaxosSmall",
    "ewd998/EWD998PCal",
    "MultiPaxos-SMR/MultiPaxos_MC_small",
    "LeastCircularSubstring/MCLeastCircularSubstringMedium",
    "GameOfLife/GameOfLife",
    "KeyValueStore/MCKVSSafetySmall",
]


# name: (description, default modes, worker counts)
TIERS = {
    "startup": ("TLC < 1s", ["compile", "interp"], [1]),
    "medium": ("TLC 1-15s", ["compile", "interp"], [1]),
    "large": ("TLC 15-150s", ["compile"], [1]),
    "scaling": (">= 100k states, 1/4/8/18 workers", ["compile"], [1, 4, 8, 18]),
    "liveness": ("temporal properties", ["compile", "interp"], [1]),
    "symmetry": ("SYMMETRY", ["compile", "interp"], [1]),
    "simulation": ("-simulate / -generate", ["compile", "interp"], [1]),
    "stress": ("fixed algorithmic stress configurations", ["compile"], [1]),
}


STRESS_MODELS = ["bench/ClockSettles", "MultiPaxos-SMR/MultiPaxos_MC"]


# Fixed liveness scaling configurations (bench/stress/NAME.cfg on a corpus
# spec), named with --models; not in the stress tier (TLC takes hours on them).
LIVENESS_MODELS = {
    "bench/RaftMongoT4": ("external", "mongo", "Replication", "RaftMongo", "MCRaftMongo.tla"),
    "bench/ReplicatedLog4x3": ("Examples", "specifications", "FiniteMonotonic", "MCReplicatedLog.tla"),
}


# Reduced message-passing configurations (bench/stress/NAME.cfg on an
# external spec): bags of messages keyed by records with sequence fields,
# the value store workload (docs/value-store.md §3).
MESSAGE_MODELS = {
    "bench/RaftMsg3": ("external", "vanlightly-raft", "standard-raft", "Raft.tla"),
    "bench/PullRaftMsg3": ("external", "vanlightly-raft", "pull-raft", "PullRaft.tla"),
    "bench/FlexibleRaftMsg3": ("external", "vanlightly-raft", "flexible-raft", "FlexibleRaft.tla"),
}


def stress_models(ids, *, stage=True):
    """Fixed configurations, independent of the ordinary corpus's TLC times."""
    out = {}
    selected_repr = [k for k in ids if k.startswith("bench/Repr")]
    if selected_repr:
        import corpus
        import tomllib
        manifest = os.path.join(ROOT, "bench", "repr-models.toml")
        if not os.path.isfile(manifest):
            # These are tracked inputs; absence means an incomplete checkout.
            raise SystemExit(f"{manifest} is not in this checkout: the reduced representation "
                             "configurations are missing; restore the tracked bench/repr-models.toml and bench/repr-configs/")
        with open(manifest, "rb") as stream:
            configurations = tomllib.load(stream)
        known = {m["id"]: m for m in corpus.models(float("inf"))}
        known.update({m["id"]: m for m in corpus.external_models(corpus.EXTERNAL_TIERS)})
        examples_present = os.path.isdir(os.path.join(corpus.EX, "specifications"))
        for k in selected_repr:
            if k not in configurations:
                sys.exit(f"unknown representation configuration {k}")
            c = configurations[k]
            cfg_path = os.path.join(ROOT, c["cfg"])
            if not os.path.isfile(cfg_path):
                raise SystemExit(f"{cfg_path} is not in this checkout: the reduced representation "
                                 "configurations are missing; restore the tracked bench/repr-models.toml and bench/repr-configs/")
            wrapper_path = os.path.join(ROOT, c["wrapper"]) if c.get("wrapper") else None
            if wrapper_path and not os.path.isfile(wrapper_path):
                raise SystemExit(f"{wrapper_path} is not in this checkout: the reduced representation "
                                 "configurations are missing; restore the tracked bench/repr-models.toml and bench/repr-configs/")
            source_id = c["source"]
            if source_id in known:
                tla = known[source_id]["tla"]
            elif not source_id.startswith(EXTERNAL_PREFIX) and not examples_present:
                tla = os.path.join(corpus.EX, "specifications", source_id + ".tla")
            else:
                sys.exit(f"unknown representation source {source_id} for {k}")
            if wrapper_path:
                stage_dir = os.path.join(ROOT, "target", "bench-models", k.split("/")[1])
                staged_tla = os.path.join(stage_dir, os.path.basename(c["wrapper"]))
                if stage:
                    if not os.path.isfile(tla):
                        raise SystemExit(
                            f"{k}: missing upstream source {tla}; fetch external corpora with scripts/fetch-external.py"
                        )
                    source_dir = os.path.dirname(tla)
                    os.makedirs(stage_dir, exist_ok=True)
                    for name in os.listdir(source_dir):
                        if name.endswith(".tla"):
                            shutil.copyfile(os.path.join(source_dir, name), os.path.join(stage_dir, name))
                    shutil.copyfile(wrapper_path, staged_tla)
                tla = staged_tla
            out[k] = {"id": k, "tla": tla, "cfg": cfg_path, "features": [], "flags": [], "tlc": {}}
    for k, tla in {**LIVENESS_MODELS, **MESSAGE_MODELS}.items():
        if k in ids:
            out[k] = {"id": k, "tla": os.path.join(TP, *tla), "cfg": os.path.join(ROOT, "bench", "stress", k.split("/")[1] + ".cfg"),
                      "features": [], "flags": [], "tlc": {}}
    if "bench/ClockSettles" in ids:
        out["bench/ClockSettles"] = {
            "id": "bench/ClockSettles",
            "tla": os.path.join(TP, "external", "tlaplus-tests", "test-model", "examples",
                                "SpecifyingSystems", "Liveness", "LiveHourClock.tla"),
            "cfg": os.path.join(ROOT, "bench", "stress", "ClockSettles.cfg"),
            "features": [], "flags": [], "tlc": {},
        }
    if "bench/FlexibleRaftReduced5" in ids:
        # Stage the wrapper beside the upstream module without modifying the
        # shared external checkout; both TLC and tlx resolve EXTENDS locally.
        tracked = [os.path.join(ROOT, "bench", "stress", name)
                   for name in ("FlexibleRaftReduced5.tla", "FlexibleRaftReduced5.cfg")]
        for path in tracked:
            if not os.path.isfile(path):
                raise SystemExit(f"bench/FlexibleRaftReduced5: missing tracked stress input {path}")
        stage_dir = os.path.join(ROOT, "target", "bench-models", "FlexibleRaftReduced5")
        upstream = os.path.join(TP, "external", "vanlightly-raft", "flexible-raft", "FlexibleRaft.tla")
        if stage:
            if not os.path.isfile(upstream):
                raise SystemExit(
                    f"bench/FlexibleRaftReduced5: missing upstream source {upstream}; fetch external corpora with scripts/fetch-external.py"
                )
            os.makedirs(stage_dir, exist_ok=True)
            shutil.copyfile(upstream, os.path.join(stage_dir, "FlexibleRaft.tla"))
            for path in tracked:
                shutil.copyfile(path, os.path.join(stage_dir, os.path.basename(path)))
        out["bench/FlexibleRaftReduced5"] = {
            "id": "bench/FlexibleRaftReduced5",
            "tla": os.path.join(stage_dir, "FlexibleRaftReduced5.tla"),
            "cfg": os.path.join(stage_dir, "FlexibleRaftReduced5.cfg"),
            "features": [], "flags": [], "tlc": {},
        }
    if "MultiPaxos-SMR/MultiPaxos_MC" in ids:
        base = os.path.join(TP, "Examples", "specifications", "MultiPaxos-SMR", "MultiPaxos_MC")
        out["MultiPaxos-SMR/MultiPaxos_MC"] = {
            "id": "MultiPaxos-SMR/MultiPaxos_MC", "tla": base + ".tla", "cfg": base + ".cfg",
            "features": [], "flags": [], "tlc": {},
        }
    return out


def declared_run_fields(model_id):
    """The run fields the corpus manifest declares for `model_id`, or `{}`.

    `{cwd, root, inputs, tlc_args}`: where the model runs, the input files it
    resolves there and the extra TLC arguments its oracle is collected with -
    read from `corpus` (the manifest reader) rather than from whichever oracle
    row is cached. A model's identity (`benchmarking.baselines.content_digest`)
    and staging therefore follow the tracked manifest, so a stale oracle row
    cannot silently drop the working directory, the trace data a run reads, or
    the fingerprint polynomial that makes its counts deterministic.
    """
    import corpus
    fields = {}
    if model_id in corpus.ROOT_RELATIVE_MODELS or model_id in corpus.MODEL_INPUTS:
        if model_id in corpus.ROOT_RELATIVE_MODELS:
            fields["cwd"] = corpus.CORPUS_ROOT_CWD
            # `corpus.EX` is the Examples root; an external model carries its
            # own root from the manifest instead. Today the set names Examples
            # models. `local_path` keeps the root in the checkout the model's
            # tla/cfg were localized to (`load_oracle`), so the run directory
            # and the spec resolve to the same tree in a worktree too.
            if not model_id.startswith(EXTERNAL_PREFIX):
                fields["root"] = local_path(corpus.EX)
        if model_id in corpus.MODEL_INPUTS:
            fields["inputs"] = list(corpus.MODEL_INPUTS[model_id])
    if model_id in corpus.TLC_ORACLE_ARGS:
        fields["tlc_args"] = list(corpus.TLC_ORACLE_ARGS[model_id])
    return fields


def oracle_tlc_args(m):
    """The extra TLC arguments one benchmark run of model `m` passes TLC.

    These are the model's oracle-collection arguments (e.g. the `-fp 0` that
    fixes the order of `VectorClocks!CausalOrder`'s concurrent log lines, so
    the `generated` count is deterministic - docs/compat.md D-25). Every
    benchmark TLC collector appends them, so a collected baseline matches the
    oracle; they are also part of the input identity
    (`benchmarking.baselines.content_digest`), so two argument sets cannot share
    one key.
    """
    return list(m.get("tlc_args") or [])


def oracle(ids=(), *, stage=True):
    """The corpus oracle (corpus/out/tlc.json), plus the external models
    (`ext/<repo>/<name>`, corpus/external.json) that `ids` names: with their
    TLC oracle result (corpus/out/tlc-ext.json) where there is one, else
    with an empty one (`tlc` {}: the medium, large and huge models have
    none; `run --tlc` measures TLC on the same machine instead), plus the
    fixed stress configurations named by `ids`, even without an oracle."""
    ext = [i for i in ids if i.startswith(EXTERNAL_PREFIX)]
    d = dict(load_oracle())
    for k, m in stress_models(ids, stage=stage).items():
        d.setdefault(k, m)
    if ext:
        from corpus import EXTERNAL_TIERS, external_models
        from oracle import issue
        manifest_ext = {m["id"]: m for m in external_models(EXTERNAL_TIERS) if m["id"] in ext}
        cached_ext = load_oracle(ids=list(manifest_ext)) if manifest_ext else {}
        single = load_oracle(ids=list(manifest_ext), oracles=["tlc-ext-1w"]) if manifest_ext else {}
        for mid, m in manifest_ext.items():
            cached = cached_ext.get(mid, {})
            if m.get("asymmetric_symmetry") and single.get(mid, {}).get("provenance", {}).get("workers") == 1:
                cached = single[mid]
            entry = {**cached, **m, "tlc": cached.get("tlc", {})}
            if problem := issue(entry):
                entry.update(tlc={}, oracle_error=problem)
            d[mid] = entry
    # The declared run layout is the tracked manifest's, not the cached row's.
    for k, m in list(d.items()):
        if fields := declared_run_fields(k):
            d[k] = {**m, **fields}
    return d


def external_selection(tiers, models=""):
    """`run --external`: the external models of the manifest tiers `tiers`
    (comma-separated; only those of `models` if given), one bench tier
    `ext-<tier>` each: {tier: [id, ...]}."""
    from corpus import EXTERNAL_TIERS, external_models
    ts = [t for t in tiers.split(",") if t]
    bad = [t for t in ts if t not in EXTERNAL_TIERS]
    if bad:
        sys.exit(f"unknown external tier(s) {bad}; known: {', '.join(EXTERNAL_TIERS)}")
    only = {k for k in models.split(",") if k}
    sel = {f"ext-{t}": [m["id"] for m in external_models((t,)) if not only or m["id"] in only] for t in ts}
    return {t: ks for t, ks in sel.items() if ks}


def cfg_text(m):
    try:
        # Without comments.
        with open(m["cfg"]) as stream:
            return re.sub(r"\\\*.*", "", stream.read())
    except OSError:
        return ""


def spread(models, n):
    """`n` of `models` (sorted by TLC time) spread evenly over the list."""
    if len(models) <= n:
        return models
    return [models[round(i * (len(models) - 1) / (n - 1))] for i in range(n)] if n > 1 else models[len(models) // 2:][:1]


def select(tiers, per_tier):
    """The models of each tier: {tier: [id, ...]}."""
    d = oracle()
    ok = {k: m for k, m in d.items() if m["tlc"].get("result") not in (None, "error") and m["tlc"].get("wall_s")}
    wall = lambda k: ok[k]["tlc"]["wall_s"]
    sim = lambda k: bool(ok[k].get("flags"))
    by_time = sorted(ok, key=wall)
    cand = {
        "startup": [k for k in by_time if not sim(k) and wall(k) < 1],
        "medium": [k for k in by_time if not sim(k) and 1 <= wall(k) < 15],
        "large": [k for k in by_time if not sim(k) and 15 <= wall(k) <= 150],
        "scaling": [k for k in by_time if not sim(k) and (ok[k]["tlc"].get("distinct") or 0) >= 100_000 and wall(k) <= 150],
        "liveness": [k for k in by_time if not sim(k) and re.search(r"\bPROPERT(Y|IES)\b", cfg_text(ok[k])) and wall(k) <= 60],
        "symmetry": [k for k in by_time if not sim(k) and re.search(r"\bSYMMETRY\b", cfg_text(ok[k])) and wall(k) <= 60],
        "simulation": [k for k in by_time if sim(k)],
    }
    return {t: list(STRESS_MODELS) if t == "stress" else spread(cand[t], per_tier) for t in tiers}


def bench_flags(m):
    """The model's simulation flags (with a fixed seed), if any."""
    flags = m.get("flags") or []
    return flags + ["-seed", "1"] if flags else []


# Models of bench/scaling/<name>.cfg (larger constants of a corpus spec), by
# id bench/<name>: the spec they configure (under Examples/specifications).
SCALE_CFGS = {
    "bench/MCLamportMutex_clock14": "lamport_mutex/MCLamportMutex.tla",
    "bench/cf1s_folklore_N5": "cf1s-folklore/cf1s_folklore.tla",
}


# The default models of `scale`: 17M-212M distinct states, TLC with 1 worker
# >= 10 minutes (the many-core scaling records under bench/history/).
SCALE_DEFAULT = [
    "dijkstra-mutex/DijkstraMutex.toolbox/Safety-4-processors/MC",
    "MultiCarElevator/ElevatorSafetyLarge",
    "MultiPaxos-SMR/MultiPaxos_MC",
    "KeyValueStore/MCKVSSafetyMedium",
    "bench/MCLamportMutex_clock14",
    "bench/cf1s_folklore_N5",
]


def scale_models(ids):
    """{id: model} of `scale`: bench/<name> (SCALE_CFGS) or an exhaustive
    model of the Examples manifests (any runtime)."""
    import corpus
    known = ({m["id"]: m for m in corpus.models(float("inf"))}
             if any(mid not in SCALE_CFGS for mid in ids) else {})
    out = {}
    for k in ids:
        if k in SCALE_CFGS:
            out[k] = {"id": k, "tla": os.path.join(corpus.EX, "specifications", SCALE_CFGS[k]),
                      "cfg": os.path.join(ROOT, "bench", "scaling", k.split("/", 1)[1] + ".cfg"), "features": [], "flags": []}
        elif k in known and not known[k]["flags"]:
            out[k] = known[k]
        else:
            sys.exit(f"unknown scaling model {k} (bench/<name> of {', '.join(SCALE_CFGS)}, or an exhaustive manifest model)")
    return out


def short_path(p):
    """Examples/... for the corpus, else relative to the checkout."""
    import corpus
    rp, tp = os.path.realpath(p), os.path.dirname(corpus.EX)
    return os.path.relpath(rp, tp) if rp.startswith(tp + os.sep) else os.path.relpath(rp, os.path.realpath(ROOT))

