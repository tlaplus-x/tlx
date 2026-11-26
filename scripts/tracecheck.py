#!/usr/bin/env python3
"""Counterexample validation by TLC (tier 3 of the contract, docs/compat.md
§0): when tlx reports a counterexample that differs from TLC's, the test
scripts (spectest.py, matrix.py) accept it only if TLC confirms that it is
a behavior of the spec that violates the reported property.

`check` writes a trace-check module next to (a copy of) the spec: it
EXTENDS the spec and adds a variable `tlx_pc`, the index of the current
state in the trace.
  - Safety counterexamples (invariant, deadlock, action property, initial
    property): Init is the spec's Init (from INIT, or the first conjuncts
    of the SPECIFICATION's definition) restricted to the first state; Next
    is the spec's Next (NEXT, or `[][Next]_v` of that definition)
    restricted, at index i < n, to the step to state i + 1; the last state
    stutters. A step that is not a step of the spec leaves state i without
    successor: TLC reports a deadlock. The invariant `tlx_Reached` (an
    action property for an action-property violation) is false exactly in
    the last state (step) if that violates the reported property (`~Inv`,
    `~ENABLED Next`, `~[A]_v` of `P == [][A]_v`): TLC must report that
    violation. A violated initial-state property: TLC must report that
    violation in the (single) state.
  - Liveness counterexamples (lassos): the module's only behavior is the
    lasso (its states, then back to the loop state, or stuttering), with
    weak fairness; TLC checks the property `Spec /\\ ~P1 /\\ ... /\\ ~Pn`
    (the reported properties) and must find no violation.
    Under VIEW the lasso only needs to be valid modulo the VIEW
    (docs/compat.md D-10): its closing step may also go to a state with the
    VIEW of some successor of the last state. Under SYMMETRY likewise modulo
    the symmetry: the closing step may go to a state that a permutation of
    the model values (one per symmetric set of the cfg, each in the
    SYMMETRY set) maps to some successor of the last state.
CONSTRAINT, ACTION_CONSTRAINT, SYMMETRY, VIEW are not in its cfg: a valid
counterexample is a behavior of the spec itself. Model values in the trace
become constants of the module (assigned to themselves in the cfg).

Limits: specs whose behavior depends on the order of strings created at
run time (tests/specs/US1, US3) behave differently once the trace's string
literals exist: there TLC's own counterexample fails the check too, and
callers treat the check as inconclusive (see `check_against`). VIEW and
SYMMETRY together are not handled (only the VIEW is taken into account).

Results are cached by a hash of the spec, its cfg and the generated module
(callers pass a dict and store it).

usage: scripts/tracecheck.py   (runs nothing; see scripts/tests/test_tracecheck.py)
"""
import tempdirs

import hashlib, itertools, math, os, re, shutil, subprocess, tempfile

from modelcheck import structure
from tlc import JAVA, jvm_env, parse, tlc_cmd
from tlxlib import run_proc

CACHE_FORMAT = "1"


def read(path):
    with open(path) as f:
        return f.read()


def write(path, text):
    with open(path, "w") as f:
        f.write(text)

# ---------------------------------------------------------------- -tool output

def messages(out):
    """The -tool messages of an output: (code, class, text)."""
    return [(int(m.group(1)), int(m.group(2)), m.group(3))
            for m in re.finditer(r"@!@!@STARTMSG (\d+):(\d) @!@!@\n(.*?)@!@!@ENDMSG \1 @!@!@", out, re.S)]


# The messages of a counterexample: TLC_STATE_PRINT2, TLC_BACK_TO_STATE,
# TLC_STATE_PRINT3; and those showing a single state after their first line
# (TLC_INVARIANT_VIOLATED_INITIAL, TLC_PROPERTY_VIOLATED_INITIAL,
# TLC_INITIAL_STATE).
TRACE = (2217, 2122, 2218)
SINGLE = {2107: "initial state:\n", 2108: "initial state:\n", 2102: "While working on the initial state:\n"}


def trace_blocks(out):
    """The counterexample of a -tool output: its states, in order, each a
    header (`2: <Next line ...>`, `3: Back to state: ...`) and the state.
    Only the first counterexample: TLC may report a second error after the
    first (its liveness check of the state whose successor violated an
    invariant, docs/compat.md D-14), the verdict is the first's."""
    blocks = []
    for code, _, text in messages(out):
        text = text.strip("\n")
        if code in TRACE:
            head, _, state = text.partition("\n")
            if blocks and code == 2217 and head.startswith("1:"):
                break
            blocks.append((head, state))
        elif code in SINGLE and SINGLE[code] in text:
            blocks.append((SINGLE[code].strip(), text.split(SINGLE[code], 1)[1]))
    return blocks


def parse_state(text):
    """A printed state (`/\\ x = 1` lines, values possibly broken over
    several lines) as [(variable, value text)], values canonicalized."""
    return structure.state(text)


def lasso(blocks):
    """A counterexample's (states, loop): states a list of [(variable,
    value)], loop None (a finite trace), "stutter" or the 1-based index of
    the state the lasso goes back to."""
    states, loop = [], None
    for head, state in blocks:
        if (target := structure.loop_target(head)) is not None:
            loop = target
        else:
            states.append(parse_state(state))
    return states, loop


def property_names(violated):
    """The names of a liveness verdict (`P`, `P and Q`, `P, Q, and R`)."""
    if not violated:
        return []
    return [n for n in re.split(r",\s*(?:and\s+)?|\s+and\s+", violated) if n]


# ---------------------------------------------------------------- the cfg

# The cfg structure and the keyword set live in modelcheck.structure; the
# checking module reads no section beyond the shared keywords (autosym_mutants,
# which reads and re-emits whole cfgs, adds POSTCONDITIONS and _PERIODIC).
cfg_sections = structure.cfg_sections
cfg_names = structure.cfg_names


# ---------------------------------------------------------------- the spec

def split_conjuncts(text):
    """The top-level `/\\` conjuncts of a formula (outside brackets)."""
    out, depth, cur, i = [], 0, "", 0
    while i < len(text):
        c = text[i]
        if c in "([{" or text.startswith("<<", i):
            depth += 1
        elif c in ")]}" or text.startswith(">>", i):
            depth -= 1
        if depth == 0 and text.startswith("/\\", i):
            out.append(cur)
            cur, i = "", i + 2
            continue
        if text.startswith("<<", i) or text.startswith(">>", i):
            cur += text[i:i + 2]
            i += 2
            continue
        cur += c
        i += 1
    out.append(cur)
    return [" ".join(c.split()) for c in out if c.strip()]


def init_next(spec_dir, name, sections):
    """The spec's (Init, Next) as TLA+ expressions, or None: from INIT /
    NEXT, or from the definition `S == Init /\\ [][Next]_v /\\ ...` of
    SPECIFICATION S in the spec's module."""
    init, nxt = cfg_names(sections, "INIT"), cfg_names(sections, "NEXT")
    if init and nxt:
        return init[0], nxt[0]
    spec = cfg_names(sections, "SPECIFICATION")
    if not spec:
        return None
    text = read(os.path.join(spec_dir, name + ".tla"))
    body = structure.definition(text, spec[0])
    if body is None:
        return None
    nm = re.search(r"\[\]\s*\[(.*?)\]_", body, re.S)
    if not nm:
        return None
    inits = [c for c in split_conjuncts(body) if not temporal(text, c)]
    return " /\\ ".join(f"({c})" for c in inits) or "TRUE", f"({' '.join(nm.group(1).split())})"


def spec_parts(spec_dir, name, sections, vars_):
    """The spec as (Init, Next, v, fairness): `Init /\\ [][Next]_v /\\
    fairness...`, from INIT / NEXT (v: `vars_`, no fairness) or from the
    conjuncts of the definition of SPECIFICATION S; None if it has no
    conjunct `[][Next]_v`."""
    init, nxt = cfg_names(sections, "INIT"), cfg_names(sections, "NEXT")
    if init and nxt:
        return init[0], nxt[0], vars_, []
    spec = cfg_names(sections, "SPECIFICATION")
    if not spec:
        return None
    text = read(os.path.join(spec_dir, name + ".tla"))
    body = structure.definition(text, spec[0])
    if body is None:
        return None
    inits, box, fair = [], None, []
    for c in split_conjuncts(body):
        m = re.fullmatch(r"\[\]\s*\[(.*)\]_(\w+|<<.*>>)", c)
        if m and box is None:
            box = (m.group(1), m.group(2))
        elif temporal(text, c):
            fair.append(c)
        else:
            inits.append(c)
    if box is None:
        return None
    return " /\\ ".join(f"({c})" for c in inits) or "TRUE", box[0], box[1], fair


def temporal(text, formula, depth=3):
    """Whether `formula` has temporal operators, also through the
    definitions it names (e.g. `Fairness`)."""
    if re.search(r"\[\]|<>|\bWF_|\bSF_|~>", formula):
        return True
    if depth == 0:
        return False
    for ident in set(re.findall(r"\b[A-Za-z_]\w*\b", formula)):
        body = structure.definition(text, ident)
        if body is not None and temporal(text, body, depth - 1):
            return True
    return False


STRING = re.compile(r'"(?:[^"\\]|\\.)*"')


def model_values(states, sections, variables):
    """The identifiers of the trace's values that need a declaration: model
    values that are not constants of the spec (those are assigned in the
    cfg: `None = None`)."""
    assigned = assigned_constants(sections)
    found = []
    for st in states:
        for _, v in st:
            v = STRING.sub('""', v)
            for m in re.finditer(r"\b([A-Za-z_]\w*)\b(?!\s*\|->)", v):
                ident = m.group(1)
                if (ident not in ("TRUE", "FALSE") and not ident[0].isdigit() and ident not in assigned
                        and ident not in variables and ident not in found):
                    found.append(ident)
    return found


def assigned_constants(sections):
    """The names the cfg assigns (`N = ...`, `N <- ...`)."""
    return set(re.findall(r"(\w+)\s*(?:=|<-)", " ".join(b for k, b in sections if k.startswith("CONSTANT"))))


def model_value_sets(sections):
    """The sets of model values the cfg assigns to constants (`P = {a, b}`):
    [[names]], in cfg order."""
    out = []
    for k, body in sections:
        if not k.startswith("CONSTANT"):
            continue
        for m in re.finditer(r"\w+\s*=\s*\{([^{}]*)\}", body):
            elems = [e.strip() for e in m.group(1).split(",") if e.strip()]
            if len(elems) > 1 and all(re.fullmatch(r"[A-Za-z_]\w*", e) and e not in ("TRUE", "FALSE") for e in elems):
                out.append(elems)
    return out


IDENT_OR_STRING = re.compile(r'"(?:[^"\\]|\\.)*"|\b[A-Za-z_]\w*\b(?!\s*\|->)')


def permute_value(text, perm):
    """A printed value with its model values renamed by `perm` (a dict;
    strings and record field names are left alone)."""
    return IDENT_OR_STRING.sub(lambda m: perm.get(m.group(0), m.group(0)), text)


# The most permutations tried for a lasso under SYMMETRY.
MAX_PERMUTATIONS = 5040


def permutations_of(sets):
    """All products of one permutation of each set: [(components, perm)],
    `components` the non-identity permutations (as [(set, image)]), `perm`
    the renaming; None if there are more than MAX_PERMUTATIONS."""
    total = 1
    for s in sets:
        total *= math.factorial(len(s))
    if total > MAX_PERMUTATIONS:
        return None
    out = []
    for images in itertools.product(*(itertools.permutations(s) for s in sets)):
        comps, perm = [], {}
        for s, img in zip(sets, images):
            if list(img) != s:
                comps.append((s, list(img)))
                perm.update(zip(s, img))
        out.append((comps, perm))
    return out


def modules_needed(states):
    """The standard modules the printed values need: Naturals (intervals),
    Integers (negative numbers), TLC (functions `a :> b @@ ...`)."""
    text = " ".join(STRING.sub('""', v) for st in states for _, v in st)
    mods = []
    if re.search(r"\d\s*\.\.\s*-?\d", text):
        mods.append("Naturals")
    if re.search(r"(?<![\w)\]}>])-\s*\d", text):
        mods.append("Integers")
    if ":>" in text or "@@" in text:
        mods.append("TLC")
    return mods


# ---------------------------------------------------------------- the check

KINDS = ("safety failure", "deadlock", "property failure", "init property failure", "liveness failure")


def trace_module(spec_dir, name, cfg, kind, states, loop=None, names=None, variables=None, simulation=False):
    """The trace-check module and cfg, and what TLC must report on them:
    (tla, cfg, expected) or (None, reason, None) when the trace cannot be
    checked this way."""
    sections = cfg_sections(cfg)
    if kind not in KINDS:
        return None, f"no counterexample to check for {kind}", None
    if not states:
        return None, "empty counterexample", None
    if variables is None:
        if cfg_names(sections, "ALIAS"):
            return None, "ALIAS: the printed states are not the variables", None
        variables = [k for k, _ in states[0]]
    rows = []
    for st in states:
        d = dict(st)
        if any(v not in d for v in variables):
            return None, f"a state lacks variables {[v for v in variables if v not in d]}", None
        rows.append("<< " + ", ".join(d[v] for v in variables) + " >>")
    # (Only the variables: an ALIAS prints other fields too.)
    states = [[(v, dict(st)[v]) for v in variables] for st in states]
    n = len(states)
    mvs = model_values(states, sections, variables)
    if kind == "liveness failure" and cfg_names(sections, "SYMMETRY") and not cfg_names(sections, "VIEW"):
        # (The permuted states of the closing step name the other model
        # values of their sets.)
        assigned = assigned_constants(sections)
        mvs += [m for ms in model_value_sets(sections) for m in ms if m not in mvs and m not in assigned]
    extends = ", ".join([name] + modules_needed(states))
    allvars = "<<" + ", ".join(variables + ["tlx_pc"]) + ">>"
    vars_ = "<<" + ", ".join(variables) + ">>"

    def assign(idx, primed):
        p = "'" if primed else ""
        return " /\\ ".join(f"{v}{p} = tlx_T[{idx}][{i + 1}]" for i, v in enumerate(variables))

    head = [f"---- MODULE tlxTC ----", f"EXTENDS {extends}"]
    if mvs:
        head.append("CONSTANTS " + ", ".join(mvs))
    head += ["VARIABLE tlx_pc", "tlx_T == << " + ",\n  ".join(rows) + " >>"]
    consts = "".join(f"{k} {b.strip()}\n" for k, b in sections if k.startswith("CONSTANT"))
    if mvs:
        consts += "CONSTANTS " + " ".join(f"{m} = {m}" for m in mvs) + "\n"
    if kind == "liveness failure":
        if loop is None:
            return None, "liveness counterexample without a loop", None
        back = n if loop == "stutter" else loop
        if not 1 <= back <= n:
            return None, f"loop target {loop} outside the trace", None
        nxt = ", ".join(str(i + 2) for i in range(n - 1)) + (", " if n > 1 else "") + str(back)
        spec = cfg_names(sections, "SPECIFICATION")
        if spec:
            orig = spec[0]
        else:
            init, nx = cfg_names(sections, "INIT"), cfg_names(sections, "NEXT")
            if not (init and nx):
                return None, "no SPECIFICATION and no INIT / NEXT", None
            orig = f"{init[0]} /\\ [][{nx[0]}]_{vars_}"
        props = names if names else cfg_names(sections, "PROPERTY", "PROPERTIES")
        if not props:
            return None, "no property to check", None
        bad = " /\\ ".join(f"~({p})" for p in props) if names else "~(" + " /\\ ".join(f"({p})" for p in props) + ")"
        extra = []
        view = cfg_names(sections, "VIEW")
        if view:
            # Valid modulo the VIEW (docs/compat.md D-10): the step closing
            # the lasso need not be a step of the spec, only go to a state
            # with the VIEW of a successor of the last state (the behavior
            # graph's nodes are VIEW classes; TLC's own lassos close so too).
            parts = spec_parts(spec_dir, name, sections, vars_)
            if parts is None:
                return None, "VIEW: cannot find the spec's Init, Next and fairness", None
            init, nx, sub, fair = parts
            subst = ", ".join(f"{v} <- tlx_T[{back}][{i + 1}]" for i, v in enumerate(variables))
            extra = [f"tlx_B == INSTANCE {name} WITH {subst}",
                     f"tlx_Close == tlx_pc = {n} /\\ tlx_pc' = {back} /\\ ENABLED (({nx}) /\\ ({view[0]})' = tlx_B!{view[0]})"]
            orig = " /\\ ".join([f"({init})", f"[][({nx}) \\/ tlx_Close]_{sub}"] + [f"({f})" for f in fair])
        elif cfg_names(sections, "SYMMETRY"):
            # Valid modulo the symmetry, as under VIEW: the closing step may
            # go to a state that a permutation in the SYMMETRY set (or a
            # product of such permutations of different sets of model
            # values) maps to a successor of the last state.
            sym = cfg_names(sections, "SYMMETRY")[0]
            parts = spec_parts(spec_dir, name, sections, vars_)
            if parts is None:
                return None, "SYMMETRY: cannot find the spec's Init, Next and fairness", None
            init, nx, sub, fair = parts
            perms = permutations_of(model_value_sets(sections))
            if perms is None:
                return None, f"SYMMETRY: more than {MAX_PERMUTATIONS} permutations of the model values", None
            target = dict(states[back - 1])
            comps, images = [], []
            for cs, perm in perms:
                comps.append("{" + ", ".join(
                    "(" + " @@ ".join(f"{a} :> {b}" for a, b in zip(s, img)) + ")" for s, img in cs) + "}")
                images.append("<< " + ", ".join(permute_value(target[v], perm) for v in variables) + " >>")
            if "TLC" not in extends.split(", "):
                head[1] += ", TLC"
            extra = [f"tlx_Perm == << " + ",\n  ".join(comps) + " >>",
                     f"tlx_Img == << " + ",\n  ".join(images) + " >>",
                     f"tlx_Close == tlx_pc = {n} /\\ tlx_pc' = {back} /\\ \\E i \\in DOMAIN tlx_Img :"
                     f" (\\A p \\in tlx_Perm[i] : p \\in {sym}) /\\ ENABLED (({nx}) /\\ {vars_}' = tlx_Img[i])"]
            orig = " /\\ ".join([f"({init})", f"[][({nx}) \\/ tlx_Close]_{sub}"] + [f"({f})" for f in fair])
        tla = "\n".join(head + extra + [
            f"tlx_Nxt == <<{nxt}>>",
            f"tlx_Init == tlx_pc = 1 /\\ {assign(1, False)}",
            f"tlx_Next == tlx_pc' = tlx_Nxt[tlx_pc] /\\ {assign('tlx_pc' + chr(39), True)}",
            f"tlx_Spec == tlx_Init /\\ [][tlx_Next]_{allvars} /\\ WF_{allvars}(tlx_Next)",
            f"tlx_Valid == ({orig}) /\\ {bad}",
            "===="]) + "\n"
        return tla, consts + "SPECIFICATION tlx_Spec\nPROPERTY tlx_Valid\n", {"result": "success"}
    if loop is not None:
        return None, "a safety counterexample with a loop", None
    inn = init_next(spec_dir, name, sections)
    if inn is None:
        return None, "cannot find the spec's Init and Next", None
    init, nx = inn
    steps = "{" + ", ".join(str(i + 1) for i in range(n - 1)) + "}"
    nxt = ", ".join(str(i + 2) for i in range(n - 1))
    # (Junction lists: the bullets of a list in the same column.)
    ors, ands = " " * len("tlx_Next == "), " " * len("tlx_Next == \\/ ")
    body = [f"tlx_Nxt == <<{nxt}>>",
            f"tlx_Init == {init} /\\ tlx_pc = 1 /\\ {assign(1, False)}",
            f"tlx_Next == \\/ /\\ tlx_pc \\in {steps}",
            f"{ands}/\\ {nx}",
            f"{ands}/\\ tlx_pc' = tlx_Nxt[tlx_pc]",
            f"{ands}/\\ {assign('tlx_pc' + chr(39), True)}"]
    body.append(f"{ors}\\/ tlx_pc = {n} /\\ UNCHANGED {allvars}")
    out = consts + "INIT tlx_Init\nNEXT tlx_Next\n"
    # tlx_Reached: violated only in the last state (step) of the trace, and
    # only if it is a violation of the spec's property. (TLC's own trace of
    # the violation is not used: TLC rebuilds it by evaluating Next again,
    # and prints a truncated trace when that fails.)
    expected = {"result": "safety failure", "violated": "tlx_Reached"}
    if kind == "safety failure":
        body.append(f"tlx_Reached == ~(tlx_pc = {n} /\\ ~({names[0]}))")
        out += "INVARIANT tlx_Reached\n"
    elif kind == "deadlock":
        if simulation:
            # (In simulation TLC reports a deadlock when no successor
            # satisfies the constraints.)
            nx += "".join(f" /\\ ({c})'" for c in cfg_names(sections, "CONSTRAINT", "CONSTRAINTS"))
            nx += "".join(f" /\\ {c}" for c in cfg_names(sections, "ACTION_CONSTRAINT", "ACTION_CONSTRAINTS"))
        body.append(f"tlx_Reached == ~(tlx_pc = {n} /\\ ~ENABLED ({nx}))")
        out += "INVARIANT tlx_Reached\n"
    elif kind == "property failure":
        act = box_action(spec_dir, name, names[0])
        if act is None or n < 2:
            return None, f"cannot find the action of {names[0]} (`{names[0]} == [][A]_v`)", None
        a, v = act
        body.append(f"tlx_Reached == [][~(tlx_pc = {n - 1} /\\ tlx_pc' = {n} /\\ ~(({a}) \\/ UNCHANGED {v}))]_{allvars}")
        out += "PROPERTY tlx_Reached\n"
        expected = {"result": "property failure", "violated": "tlx_Reached"}
    else:
        if n != 1:
            return None, f"a violation of an initial-state property with {n} states", None
        # (TLC names the violated property by its location in this case:
        # the cfg's properties are checked.)
        out += "PROPERTY " + " ".join(cfg_names(sections, "PROPERTY", "PROPERTIES")) + "\n"
        expected = {"result": "init property failure"}
    return "\n".join(head + body + ["===="]) + "\n", out, expected


def box_action(spec_dir, name, prop):
    """(A, v) of the definition `prop == [][A]_v` in the spec's module, or
    None."""
    body = structure.definition(read(os.path.join(spec_dir, name + ".tla")), prop)
    if body is None:
        return None
    am = re.fullmatch(r"\[\]\s*\[(.*)\]_(\w+|<<.*>>)", " ".join(body.split()))
    return (am.group(1), am.group(2)) if am else None


def java_available():
    return os.path.exists(JAVA) or shutil.which(JAVA) is not None


def check(spec_dir, name, cfg, kind, states, loop=None, names=None, *, variables=None, simulation=False, cache=None,
          timeout=300):
    """Whether TLC confirms the counterexample (states, loop) of `kind`
    violating `names` (the invariant / property; for liveness the reported
    properties, None: some PROPERTY of the cfg) for the spec `name` in
    `spec_dir` with cfg text `cfg`. `variables`: the spec's variables, in
    the order of the module (default: the printed ones; needed with an
    ALIAS); `simulation`: the counterexample of a simulation (a deadlock
    is then one under the constraints). Returns (verdict, detail), verdict one of
      "valid"       TLC confirms;
      "invalid"     TLC rejects it (detail: what TLC reported);
      "unchecked"   it cannot be checked (no java; the trace cannot be
                    expressed as a trace-check module: detail says why);
      "error"       the trace-check module is rejected by SANY / TLC
                    (a problem of this script, not of the trace).
    `cache` (a dict, or None) maps a hash of the inputs to [verdict, detail]."""
    tla, tcfg, expected = trace_module(spec_dir, name, cfg, kind, states, loop, names, variables, simulation)
    if tla is None:
        return "unchecked", tcfg
    spec_text = read(os.path.join(spec_dir, name + ".tla"))
    key = hashlib.sha1("\0".join([CACHE_FORMAT, spec_text, cfg, tla, tcfg]).encode()).hexdigest()[:20]
    if cache is not None and key in cache:
        return tuple(cache[key])
    if not java_available():
        return "unchecked", "no java (set TLX_JAVA)"
    with tempdirs.TemporaryDirectory(prefix="tlx-tracecheck-") as tmp:
        d = os.path.join(tmp, "specs")
        shutil.copytree(spec_dir, d, ignore=shutil.ignore_patterns("tlc", "*.out", "*_TTrace_*", "states"))
        write(os.path.join(d, "tlxTC.tla"), tla)
        write(os.path.join(d, "tlxTC.cfg"), tcfg)
        features = ["action composition"] if "\\cdot" in spec_text else []
        cmd = tlc_cmd("tlxTC.tla", ["-workers", "1", "-tool", "-config", "tlxTC.cfg"], features, state_dir=os.path.join(tmp, "states"))
        try:
            p = run_proc(cmd, timeout, cwd=d, env=jvm_env())
        except subprocess.TimeoutExpired:
            return "unchecked", f"TLC timed out after {timeout} s"
    out = p.stdout + p.stderr
    verdict = judge(out, p.returncode, expected)
    if cache is not None and verdict[0] in ("valid", "invalid"):
        cache[key] = list(verdict)
    return verdict


def check_against(spec_dir, name, cfg, kind, got, names, want, want_names, **options):
    """`check` for tlx's counterexample `got` = (states, loop) violating
    `names`, with TLC's counterexample `want` (violating `want_names`) as the
    control: if TLC rejects tlx's counterexample, it checks its own, and
    if that fails too, the check is inconclusive ("unchecked": the
    trace-check module cannot express the spec's counterexamples, e.g. under
    VIEW / SYMMETRY). Returns (verdict, detail) as `check`; `options` are
    those of `check`."""
    verdict, why = check(spec_dir, name, cfg, kind, got[0], got[1], names, **options)
    if verdict != "invalid" or want is None:
        return verdict, why
    control, cwhy = check(spec_dir, name, cfg, kind, want[0], want[1], want_names, **options)
    if control == "valid":
        return verdict, why
    return "unchecked", f"TLC's own counterexample fails the check too ({control}: {cwhy[:200]})"


def judge(out, rc, expected):
    r = parse(out, 0, rc)
    if "Semantic errors" in out or "Parse Error" in out or "*** Errors:" in out or r.get("result") == "unknown":
        return "error", "TLC rejects the trace-check module: " + (r.get("error") or out[-600:]).strip()
    got = {"result": r.get("result")}
    if "violated" in expected:
        got["violated"] = r.get("violated")
    if got == expected:
        return "valid", ""
    what = r.get("error", "") if r.get("result") == "error" else ""
    return "invalid", f"TLC: {got} (expected {expected}) {what}".strip()
