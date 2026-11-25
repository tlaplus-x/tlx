"""Corpus selection is a manifest operation; oracle records are evidence only."""
import datetime
import hashlib
import os
import platform


def cfg_digest(model):
    with open(model["cfg"], "rb") as source:
        return hashlib.sha256(source.read()).hexdigest()


def provenance(model, workers, result):
    return {"cfg_digest": cfg_digest(model), "workers": workers,
            "tlc_version": result.get("tlc_version", "unknown"),
            "machine": {"system": platform.system(), "release": platform.release(),
                        "arch": platform.machine(), "cpus": os.cpu_count()},
            "date": datetime.datetime.now(datetime.timezone.utc).isoformat()}


def issue(model):
    r = model.get("tlc", {})
    if r.get("result") in (None, "unknown", "timeout", "collection error"):
        return "missing or incomplete TLC oracle; refresh shared oracles with: sh harness/agent_setup.sh --refresh-oracles"
    if r.get("result") == "error" and ("exit" not in r or r.get("exit", 0) < 0):
        return "TLC oracle collection error"
    if r.get("exit", 0) < 0 or (r.get("result") == "success" and r.get("exit", 0) != 0):
        return "TLC oracle did not complete"
    p = model.get("provenance")
    if p:
        try:
            if p.get("cfg_digest") != cfg_digest(model):
                return "stale TLC oracle: cfg digest changed"
        except OSError as error:
            return f"cannot verify TLC oracle cfg: {error}"
    if model.get("asymmetric_symmetry") and (p or {}).get("workers") != 1:
        return "missing authoritative TLC -workers 1 oracle for non-equivariant SYMMETRY; refresh shared oracles with: sh harness/agent_setup.sh --refresh-oracles"
    return None


def select_models(filter="", ids=(), oracles=(), tiers=""):
    from corpus import models, external_models, EXTERNAL_TIERS, HUGE_MAX_RUNTIME, HUGE_MIN_RUNTIME
    from corpus import INVALID_UPSTREAM_MODELS
    from tlxlib import load_oracle
    ids = {i for i in (ids.split(",") if isinstance(ids, str) else ids) if i}
    names = [n for n in (oracles.split(",") if isinstance(oracles, str) else oracles) if n]
    ts = {t for t in (tiers.split(",") if isinstance(tiers, str) else tiers) if t}
    if ts - set(EXTERNAL_TIERS):
        raise ValueError(f"unknown external tiers: {sorted(ts - set(EXTERNAL_TIERS))}")
    selected = models(60)
    if ids or "tlc-large" in names:
        selected += models(700, 61)
    if ids or "tlc-huge" in names:
        selected += models(HUGE_MAX_RUNTIME, HUGE_MIN_RUNTIME)
    external = filter.startswith("ext/") or any(i.startswith("ext/") for i in ids) or any(n.startswith("tlc-ext") for n in names)
    if external:
        if not ts:
            ts = set(EXTERNAL_TIERS) if ids else ({"small", "medium"} if filter.startswith("ext/") or "tlc-ext" in names else set())
            for tier in EXTERNAL_TIERS:
                if any(tier in n.split("-")[2:] for n in names if n.startswith("tlc-ext-")):
                    ts.add(tier)
        selected += external_models(ts)
    data = load_oracle(filter, ids, names)
    single = load_oracle(filter, ids, ["tlc-ext-1w"]) if external else {}
    result = {}
    for m in selected:
        k = m["id"]
        if filter in k and (not ids or k in ids):
            if m.get("asymmetric_symmetry") and single.get(k, {}).get("provenance", {}).get("workers") == 1:
                data[k] = single[k]
            # Manifest paths, flags, worker requirements and tiers win over old caches.
            result[k] = {**data.get(k, {}), **m, "tlc": data.get(k, {}).get("tlc", {})}
    for k in ids - result.keys():
        result[k] = {"id": k, "tlc": {}, "selection_error": INVALID_UPSTREAM_MODELS.get(
            k, "requested id absent from selected manifest")}
    return result
