"""State-level TLC contract judgments and narrow known-defect classifiers."""
import os
from contract import compare as compare_contract
from modelcheck import fuzz_expr as fx
from modelcheck.results import must
import tracecheck
from .constants import SAFETY


def paranoid_text(out):
    i = out.find("TLX_PARANOID")
    return out[max(0, i - 200):i + 600] if i >= 0 else ""



def judge(d, name, want, got, workers, validated, interp=None):
    """The differences between `want` (TLC's result, or the interpreter's)
    and `got` by the contract's tiers: (differences, note). A counterexample
    that differs from TLC's must be valid for TLC, with any worker count."""
    if got.get("result") == "timeout":
        return ["timeout"], ""
    if "TLX_PARANOID" in got.get("out", ""):
        return ["paranoid"], paranoid_text(got["out"])
    if got.get("result") in (None, "unknown") or (got.get("exit") or 0) < 0:
        return ["crash"], got.get("out", "")[-800:]
    c = compare_contract(want, got, workers=workers, allow_unnamed_liveness=workers == 1)
    diffs = list(c.differs)
    if diffs:
        return diffs, ""
    result = want["result"]
    if result in SAFETY:
        if got["trace"] == want["trace"]:
            return [], ""
        names = [got["violated"]]
    elif result == "liveness failure":
        if (got["trace"], got["violated"]) == (want["trace"], want["violated"]):
            return [], ""
        names = tracecheck.property_names(got["violated"])
        if not names and want["violated"] is not None:
            return ["violated"], "tlx names no violated property"
        names = names or None
    else:
        return [], ""
    if interp is not None:
        # (Against the interpreter, only TLC can judge a differing trace.)
        return [], ""
    cfg = tracecheck.read(os.path.join(d, name + ".cfg"))
    want_names = tracecheck.property_names(want["violated"]) if result == "liveness failure" else [want["violated"]]
    verdict, why = tracecheck.check_against(d, name, cfg, result, got["lasso"], names, want["lasso"], want_names,
                                            cache=validated)
    if verdict in ("valid", "unchecked"):
        return [], f"trace differs, {verdict}" + (f": {why}" if why else "")
    return ["trace"], f"trace differs: {verdict}: {why}"



SHOW = ("result", "violated", "distinct", "generated", "depth")



# Known open differences: (id, reason, predicate(TLC output, tlx output, mode,
# spec/cfg text, differences)). Keep each minimized regression and remove its
# classifier when fixed; documented TLC defects retain their compatibility ID.
KNOWN = [
    ("D-27",
     "TLC diagnostic initial-state replay reuses the FPSet and changes error-time counts or the first error; "
     "tlx retains the original liveness evaluation error (docs/compat.md D-27)",
     lambda tlc, tlx, mode, text, diffs: "While working on the initial state" in tlc
     and "Live ==" in text and "Computing initial states" in tlx and must(tlx, None).get("result") == "error"
     and set(diffs) <= {"result", "violated", "distinct", "generated", "depth", "trace length"}),
    ("D-29",
     "TLC accepts a literal constant VIEW because preprocessing skips it; tlx consistently rejects pure "
     "constant VIEW definitions (docs/compat.md D-29)",
     lambda tlc, tlx, mode, text, diffs: "cannot be a constant" in tlx and "view function" in tlx
     and must(tlc, None).get("result") == "success"
     and set(diffs) <= {"result", "distinct", "generated", "depth"}),
    ("D-28",
     "TLC defect (docs/compat.md D-28): TLC's counterexample of an action property lacks the violating successor (one "
     "state) when rebuilding the step fails in another branch; tlx prints both states",
     lambda tlc, tlx, mode, text, diffs: diffs == ["trace length"] and "Action property" in tlc
     and "Max({})" in text and len(tracecheck.trace_blocks(tlc)) == 1),
]



def known_issue(tlc_out, tlx_out, mode, text, diffs):
    """The KNOWN entry (id, reason) a mismatch matches (`text`: the module and the cfg)."""
    return next(((k, why) for k, why, pred in KNOWN if pred(tlc_out, tlx_out, mode, text, diffs)), None)



def heterogeneous_issue(want, got, mode, op, diffs, tlc_out, tlx_out, kinds=()):
    """Recognize D-31 without hiding errors or compiled/interpreter mismatches."""
    if (want.get("result") == "error" and got.get("result") == "success"
            and set(diffs) <= {"result", "distinct", "generated", "depth"}
            and fx.function_comparison_defect(kinds, tlc_out)):
        return "heterogeneous-function-comparison-defect"
    return None



def brief(r):
    return {k: r.get(k) for k in SHOW if r.get(k) is not None}
