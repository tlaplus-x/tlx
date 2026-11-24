"""Static check: every option a driver script parses reaches a consumer.

Root cause this guards (2026-10-08 step-back on the harness): an option can be
parsed and then silently ignored. ``cloud_verify.py`` dropped ``--suites`` when
``--bench`` was given (now refused; see ``test_cloud_verify``), and
``tlcsuite.py`` accepted ``--strict``/``--suite`` without ever reading them.

The check parses each driver, collects the ``dest`` of every ``add_argument``
call (including ones made by a local helper, by one imported from ``tlxlib``, or
by the module that owns the driver's parser -- see ``PARSER_OWNERS`` -- or by a
module its extracted consumers moved to -- see ``CONSUMER_OWNERS``), then
collects every attribute of a parsed namespace that is actually read in the
driver -- following the namespace into whatever function it is passed to, inside
the driver's own tree or in any module its imports name, nested packages
included. An option whose ``dest`` is never read anywhere is a silent no-op:
give it a consumer, delete it, or declare it an alternative in an ``argparse``
mutually exclusive group whose consuming flag is read.

It is deliberately a fixed list of drivers, not auto-discovery: following every
script's helpers would need type inference the harness does not have and would
report the bench suite's own modules (owned elsewhere) as orphans.
"""
import ast
import importlib
import os
import re
import shlex
import unittest

import testkit

SCRIPTS = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
#: The product drivers. The agent harness's own entry points (`harness/
#: merge_gate.py`, `harness/done_check.py`) used to be here; they moved into the
#: untracked harness, whose layout this product check does not follow.
DRIVERS = ["cloud_verify", "bench", "verify", "spectest", "difftest", "tlcsuite"]

# Drivers whose CLI parser was extracted into a module of its own, so there is one
# parser for the entry point and every preflight (HARNESS-02). The owner's
# ``add_argument`` calls, defaults and help ARE that driver's parser surface:
# without this map a check that reads only the driver's own tree finds no options
# at all for it and passes vacuously, which is exactly what the 2026-10-09
# extraction of bench's parser into benchmarking/cli.py did. Keys are driver
# modules, values paths relative to scripts/.
PARSER_OWNERS = {"bench": os.path.join("benchmarking", "cli.py")}

# Drivers whose option consumers were extracted into modules of their own, by
# path relative to scripts/ and looked up in NESTED_TREES like the owner above:
# the dest analysis follows them, or every option whose read moved there is
# reported as a silent no-op (HARNESS-13, the cloud_verify phases move).
CONSUMER_OWNERS = {
    "cloud_verify": [os.path.join("cloud", "setup.py"), os.path.join("cloud", "remote.py"),
                     os.path.join("cloud", "session.py")],
}


def _parse_all():
    """(trees, global-functions, nested trees) for every non-test script in scripts/.

    Top-level modules are keyed by their module name and nested package modules by
    their source-relative path. ``TREES`` and ``GLOBAL_FUNCS`` keep only the
    top-level ones, so a name a nested module defines is reached through the
    import statement that names it (``_module_tree``) rather than globally: the
    nested trees are what a driver's own import graph resolves to, which is what
    keeps this check from needing an edit every time a file moves into a package
    (HARNESS-13).
    """
    trees, funcs, nested = {}, {}, {}
    for entry in sorted(os.listdir(SCRIPTS)):
        if not entry.endswith(".py") or entry.startswith("test_"):
            continue
        with open(os.path.join(SCRIPTS, entry)) as source:
            try:
                tree = ast.parse(source.read())
            except SyntaxError:
                continue
        trees[entry[:-3]] = tree
        for node in ast.walk(tree):
            if isinstance(node, ast.FunctionDef):
                funcs.setdefault(node.name, node)
    for base, dirs, names in os.walk(SCRIPTS):
        dirs[:] = [d for d in dirs if d != "__pycache__"]
        for entry in sorted(names):
            if not entry.endswith(".py") or entry.startswith("test_"):
                continue
            path = os.path.join(base, entry)
            relative = os.path.relpath(path, SCRIPTS)
            if relative == entry:
                continue
            with open(path) as source:
                try:
                    nested[relative] = ast.parse(source.read())
                except SyntaxError:
                    continue
    return trees, funcs, nested


TREES, GLOBAL_FUNCS, NESTED_TREES = _parse_all()


def _calls(node):
    return (c for c in ast.walk(node) if isinstance(c, ast.Call))


def _add_argument_calls(node):
    return (c for c in _calls(node)
            if isinstance(c.func, ast.Attribute) and c.func.attr == "add_argument")


def _strings(call):
    return [a.value for a in call.args if isinstance(a, ast.Constant) and isinstance(a.value, str)]


def _dest(call):
    """The argparse dest of one ``add_argument`` call (explicit, or from the longest flag)."""
    for keyword in call.keywords:
        if keyword.arg == "dest" and isinstance(keyword.value, ast.Constant):
            return keyword.value.value
    flags = [s for s in _strings(call) if s.startswith("-")]
    if flags:
        return max(flags, key=len).lstrip("-").replace("-", "_")
    positional = _strings(call)
    return positional[0] if positional else None


def _function_defs(tree):
    return {n.name: n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)}


def _local_functions(name):
    return _function_defs(TREES[name])


def _parser_trees(driver):
    """The trees that define `driver`'s parser: its own, then its owner module's."""
    owner = PARSER_OWNERS.get(driver)
    return [TREES[driver]] + ([NESTED_TREES[owner]] if owner else [])


def _consumer_trees(driver):
    """The trees of `driver`'s extracted consumer modules (CONSUMER_OWNERS).

    They are scanned as if they were part of the driver's own tree: a parsed
    namespace read in the code the driver's phases moved to is still consumed.
    """
    return [NESTED_TREES[path] for path in CONSUMER_OWNERS.get(driver, ())]


def _owner_bindings(driver):
    """Local name -> owner tree for the parser-owner module `driver` imports.

    ``from benchmarking import cli as bench_cli`` binds ``bench_cli``, so a call
    through it resolves like a local def and the namespace it receives is followed
    into the owner's own reads.
    """
    owner = PARSER_OWNERS.get(driver)
    if owner is None:
        return {}
    dotted = owner[:-3].replace(os.sep, ".")
    for node in ast.walk(TREES[driver]):
        if isinstance(node, ast.ImportFrom) and node.module:
            for alias in node.names:
                if f"{node.module}.{alias.name}" == dotted:
                    return {alias.asname or alias.name: NESTED_TREES[owner]}
        elif isinstance(node, ast.Import):
            for alias in node.names:
                if alias.name == dotted:
                    return {(alias.asname or alias.name).split(".")[0]: NESTED_TREES[owner]}
    return {}


def _module_tree(dotted):
    """The tree of a dotted module name, nested package modules included.

    ``NESTED_TREES`` is keyed by source-relative path, so a module that moved into
    ``scripts/<package>/`` is still found under the name its importer spells: the
    driver's own import graph is what resolves it, and no list has to be edited
    when the next file moves (HARNESS-13).
    """
    if dotted in TREES:
        return TREES[dotted]
    return NESTED_TREES.get(dotted.replace(".", os.sep) + ".py")


def _module_attribute(tree, attribute):
    """The FunctionDef a module's attribute names: a def in it, or a name it re-exports.

    ``bench.tlx`` is the first shape. ``bench.run_bench`` is the second: a pass in
    ``scripts/benchmarking/commands/`` calls its collaborators through the entry
    point module, which imports them, so the attribute names the owning module's def.
    """
    defs = _function_defs(tree)
    if attribute in defs:
        return defs[attribute]
    module = _imports_of(tree).get(attribute)
    inner = _module_tree(module) if module else None
    return _function_defs(inner).get(attribute) if inner is not None else None


def _imports_of(tree):
    """Local name -> module name for one tree's ``import M`` / ``from M import X``."""
    out = {}
    for node in ast.walk(tree):
        if isinstance(node, ast.ImportFrom) and node.module:
            for alias in node.names:
                qualified = node.module + "." + alias.name
                out[alias.asname or alias.name] = qualified if _module_tree(qualified) is not None else node.module
        elif isinstance(node, ast.Import):
            for alias in node.names:
                out[alias.asname or alias.name.split(".")[0]] = alias.name.split(".")[0]
    return out


def _imports(name):
    """Local name -> module name for ``import M`` / ``from M import X``."""
    return _imports_of(TREES[name])


def _resolve(driver, call, imports, local, owners=None):
    """The FunctionDef a call names: a local def, one the driver imports (nested
    packages included), one the driver reaches through its parser-owner module
    (``bench_cli.build_parser(...)``), or one of the driver's own module attributes
    (``bench.run_bench(...)``, a pass the entry point imports from its owner)."""
    func = call.func
    if isinstance(func, ast.Attribute) and isinstance(func.value, ast.Name) and owners:
        tree = owners.get(func.value.id)
        if tree is not None:
            return _function_defs(tree).get(func.attr)
    if isinstance(func, ast.Name):
        if func.id in local:
            return local[func.id]
        module = imports.get(func.id)
        tree = _module_tree(module) if module else None
        if tree is not None:
            return _function_defs(tree).get(func.id)
        return GLOBAL_FUNCS.get(func.id)
    if isinstance(func, ast.Attribute) and isinstance(func.value, ast.Name):
        module = imports.get(func.value.id)
        tree = _module_tree(module) if module else (TREES.get(driver) if func.value.id == driver else None)
        if tree is not None:
            resolved = _module_attribute(tree, func.attr)
            if resolved is not None:
                return resolved
        return GLOBAL_FUNCS.get(func.attr)
    return None


def _adder_dests(function):
    """dests added by ``add_argument`` calls owned by `function` (a local or tlxlib def)."""
    dests = {}
    for call in _add_argument_calls(function):
        dest = _dest(call)
        if dest:
            dests.setdefault(dest, _strings(call))
    return dests


def _group_dests(trees):
    """dests that belong to an ``argparse`` mutually exclusive group with a consumed sibling."""
    groups = {}
    for tree in trees:
        for node in ast.walk(tree):
            if (isinstance(node, ast.Assign) and isinstance(node.value, ast.Call)
                    and isinstance(node.value.func, ast.Attribute)
                    and node.value.func.attr == "add_mutually_exclusive_group"):
                for target in node.targets:
                    if isinstance(target, ast.Name):
                        groups[target.id] = set()
        for call in _add_argument_calls(tree):
            owner = call.func.value
            if isinstance(owner, ast.Name) and owner.id in groups:
                dest = _dest(call)
                if dest:
                    groups[owner.id].add(dest)
    return groups


def _namespaces(tree):
    """Names bound from a ``...parse_args()`` call, including a pair target
    (``parser, a = cli.parse_args(argv)``)."""
    names = set()
    for node in ast.walk(tree):
        if isinstance(node, (ast.Assign, ast.AnnAssign)) and isinstance(node.value, ast.Call):
            func = node.value.func
            if isinstance(func, ast.Attribute) and func.attr == "parse_args":
                targets = node.targets if isinstance(node, ast.Assign) else [node.target]
                for target in targets:
                    if isinstance(target, ast.Name):
                        names.add(target.id)
                    elif isinstance(target, ast.Tuple):
                        names.update(e.id for e in target.elts if isinstance(e, ast.Name))
    return names


def _held_handlers(driver, imports):
    """The defs of imported modules the driver's own tree holds a reference to.

    The entry point dispatches through a table (``{"run": cmd_run, ...}[a.cmd](a)``),
    so a handler that moved into a package module is not a call this check can
    follow: it is a name the driver holds. Each such name resolves through the
    driver's imports to the module that defines it, whose body is where the pass
    reads the options -- without this the whole pass reads as dead options
    (HARNESS-13). A name the driver *calls* is left out: the call-following below
    already reaches it.
    """
    called = {node.func.id for node in _calls(TREES[driver]) if isinstance(node.func, ast.Name)}
    out, seen = [], set()
    for node in ast.walk(TREES[driver]):
        if not isinstance(node, ast.Name) or not isinstance(node.ctx, ast.Load) or node.id in called:
            continue
        module = imports.get(node.id)
        tree = _module_tree(module) if module else None
        definition = _function_defs(tree).get(node.id) if tree is not None else None
        if definition is not None and id(definition) not in seen:
            seen.add(id(definition))
            out.append(definition)
    return out


def _reachable_consumers(driver):
    """(dests, consumed) for one driver, following the namespace into callees."""
    tree = TREES[driver]
    trees = _parser_trees(driver)
    owners = _owner_bindings(driver)
    imports, local = _imports(driver), _local_functions(driver)
    dests = {}
    for call in (c for parser_tree in trees for c in _add_argument_calls(parser_tree)):
        dest = _dest(call)
        if dest:
            dests.setdefault(dest, _strings(call))
    for call in _calls(tree):
        func = call.func
        helper = None
        if isinstance(func, ast.Name) and func.id in local:
            helper = local[func.id]
        elif isinstance(func, ast.Name) and imports.get(func.id) == "tlxlib":
            helper = _local_functions("tlxlib").get(func.id)
        if helper is not None:
            for dest, flags in _adder_dests(helper).items():
                dests.setdefault(dest, flags)

    namespaces = _namespaces(tree)
    consumed, wildcard = set(), False
    bodies, seen = [tree, *_held_handlers(driver, imports), *_consumer_trees(driver)], set()
    changed = True
    while changed:
        changed = False
        for body in bodies:
            for node in ast.walk(body):
                if (isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name)
                        and node.value.id in namespaces):
                    consumed.add(node.attr)
                if (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
                        and node.func.id == "getattr" and len(node.args) > 1
                        and isinstance(node.args[0], ast.Name) and node.args[0].id in namespaces
                        and isinstance(node.args[1], ast.Constant)):
                    consumed.add(node.args[1].value)
                if (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
                        and node.func.id == "vars" and node.args
                        and isinstance(node.args[0], ast.Name) and node.args[0].id in namespaces):
                    wildcard = True
                if not isinstance(node, ast.Call):
                    continue
                callee = _resolve(driver, node, imports, local, owners)
                if callee is None or id(callee) in seen:
                    continue
                params = [a.arg for a in callee.args.args]
                offset = len(params) - len(node.args)
                passed = False
                for index, arg in enumerate(node.args):
                    if isinstance(arg, ast.Name) and arg.id in namespaces:
                        position = index + offset
                        if 0 <= position < len(params):
                            passed = True
                            if params[position] not in namespaces:
                                namespaces.add(params[position])
                                changed = True
                for keyword in node.keywords:
                    if (keyword.arg and isinstance(keyword.value, ast.Name)
                            and keyword.value.id in namespaces and keyword.arg in params):
                        passed = True
                        if keyword.arg not in namespaces:
                            namespaces.add(keyword.arg)
                            changed = True
                if passed:
                    seen.add(id(callee))
                    bodies.append(callee)
    return dests, consumed, wildcard


def orphan_options(driver):
    """The dests the driver parses but never reads (the silent no-ops)."""
    dests, consumed, wildcard = _reachable_consumers(driver)
    if wildcard:
        return []
    declared = set()
    for members in _group_dests(_parser_trees(driver)).values():
        if members & consumed:
            declared |= members
    return sorted(dest for dest in dests if dest not in consumed and dest not in declared)


# --- Help text must match what argparse accepts (c-r07, 2026-10-08) ----------
#
# The root cause behind a stale sentence in ``cloud_verify.py``: its ``--help``
# still offered "run the suites as a --then pass" next to a --bench refusal,
# but argparse refuses ``--then`` with ``--bench``. Help text is prose, so it
# drifts from the parser silently; this rule runs it through the parser.

REFUSAL_MARKERS = ("cannot be combined", "mutually exclusive", "refused",
                   "would be ignored", "never execute", "never run",
                   "instead of", "incompatible", "only with")

# The ways a help unit may state that two options are alternatives. Compared
# against the whitespace-collapsed text (``_flat``), the normalization the
# documented-example check already uses: help prose is wrapped by hand, so
# whether a sentence is recognized must not depend on where its lines break.
_ALT_PATTERNS = (
    r"{a}\s*(?:and|or|,|/|\|)\s*{b}",
    r"{a}\s+cannot be combined with\s+{b}",
    r"{a}\s+given with\s+{b}[^.;]{{0,40}}(?:is|are|would be)\s+(?:refused|ignored|never)",
    r"{a}\s*(?:and|or)\s*{b}\s+(?:are|is)\s+(?:mutually exclusive|refused|incompatible)",
)

# Several options grouped against one: "A and B cannot be combined with C"
# states the pair for each of the first two, and it is how a wrapped sentence
# usually reads ("--suites and --oracle cannot be\ncombined with --bench").
_GROUP_REFUSAL = re.compile(r"(--[\w-]+(?:\s*(?:,|and|or)\s+--[\w-]+)+)\s+cannot be combined with\s+(--[\w-]+)")

FLAG_RE = re.compile(r"(?<![\w-])--[a-z][a-z0-9-]*")


def _option_flags(tree):
    """Every long flag one ``add_argument``-owning tree defines."""
    flags = set()
    for call in _add_argument_calls(tree):
        flags.update(s for s in _strings(call) if s.startswith("--"))
    return flags


def _driver_flags(driver):
    """Every long flag the driver's parser defines (its own tree and its owner's)."""
    flags = set()
    for tree in _parser_trees(driver):
        flags.update(_option_flags(tree))
    return flags


def _group_flags(trees):
    """Options of each ``add_mutually_exclusive_group`` (by the flags it holds)."""
    groups = {}
    for tree in trees:
        for node in ast.walk(tree):
            if (isinstance(node, ast.Assign) and isinstance(node.value, ast.Call)
                    and isinstance(node.value.func, ast.Attribute)
                    and node.value.func.attr == "add_mutually_exclusive_group"):
                for target in node.targets:
                    if isinstance(target, ast.Name):
                        groups[target.id] = set()
        for call in _add_argument_calls(tree):
            owner = call.func.value
            if isinstance(owner, ast.Name) and owner.id in groups:
                groups[owner.id].update(s for s in _strings(call) if s.startswith("--"))
    return groups


def _error_texts(tree):
    texts = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr == "error":
            texts.extend(a.value for a in node.args
                         if isinstance(a, ast.Constant) and isinstance(a.value, str))
    return texts


def exclusive_pairs(driver):
    """The option pairs ``driver`` refuses: its groups plus its ``ap.error`` claims."""
    known = _driver_flags(driver)
    pairs = set()
    for members in _group_flags(_parser_trees(driver)).values():
        members = sorted(members)
        for i, first in enumerate(members):
            for second in members[i + 1:]:
                pairs.add((first, second))
    for text in _error_texts(TREES[driver]):
        for pattern in (r"(--[\w-]+)\s+cannot be combined with\s+(--[\w-]+)",
                        r"(--[\w-]+)\s+and\s+(--[\w-]+)\s+are mutually exclusive"):
            for first, second in re.findall(pattern, text):
                if first in known and second in known:
                    pairs.add(tuple(sorted((first, second))))
    return pairs


def _help_strings(tree):
    units = []
    for node in ast.walk(tree):
        if (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
                and node.func.attr == "add_argument"):
            for keyword in node.keywords:
                if keyword.arg == "help" and isinstance(keyword.value, ast.Constant)                         and isinstance(keyword.value.value, str):
                    units.append(("help", keyword.value.value))
    return units


def help_units(driver):
    """(kind, text) for every help unit of ``driver``: docstring paragraphs and the
    option help of its own parser surface (including the owner module's)."""
    tree = TREES[driver]
    units = []
    doc = ast.get_docstring(tree)
    if doc:
        units.extend(("docstring", part) for part in re.split(r"\n\s*\n", doc))
    for parser_tree in _parser_trees(driver):
        units.extend(_help_strings(parser_tree))
    return [(kind, text) for kind, text in units if "usage:" not in text]


def _marked_as_alternatives(text, first, second):
    """Whether ``text`` states that ``first`` and ``second`` are alternatives.

    Matched against the whitespace-collapsed text, so a sentence that says it in
    one line and the same sentence re-wrapped between two flags give the same
    answer; the earlier literal match made recognition depend on where the line
    broke, and a refusal wrapped as ``--suites and --oracle cannot be\\ncombined
    with --bench`` was read as the help promising that combination (H-03 item
    3). Collapsing is not enough on its own for that shape - two options stated
    together against a third - so the grouped form is matched by its own
    pattern, and both options it groups count as marked against the third.
    """
    flat = _flat(text)
    for pattern in _ALT_PATTERNS:
        if re.search(pattern.format(a=first, b=second), flat) or re.search(pattern.format(a=second, b=first), flat):
            return True
    for group, refused in _GROUP_REFUSAL.findall(flat):
        for flag in FLAG_RE.findall(group):
            if {flag, refused} == {first, second}:
                return True
    return False


def undocumented_refusals(driver):
    """Option pairs a help unit refuses and does not name as the alternatives.

    A help unit that states a refusal (``REFUSAL_MARKERS``) and names two options
    of the driver which argparse refuses together must say *that* about those
    two options; otherwise the prose promises a combination the parser rejects
    (the 2026-10-08 ``--bench``/``--then`` case). Each finding is
    ``(kind, collapsed text, pairs, wrapped)``: ``wrapped`` says the unit spans
    more than one line, so a reader sees the text was wrapped rather than
    reading the collapsed quote as what the help literally says.
    """
    known, exclusive = _driver_flags(driver), exclusive_pairs(driver)
    found = []
    for kind, text in help_units(driver):
        lowered = text.lower()
        if not any(marker in lowered for marker in REFUSAL_MARKERS):
            continue
        named = sorted({flag for flag in FLAG_RE.findall(text) if flag in known})
        unmarked = [(a, b) for i, a in enumerate(named) for b in named[i + 1:]
                    if tuple(sorted((a, b))) in exclusive and not _marked_as_alternatives(text, a, b)]
        if unmarked:
            collapsed = _flat(text)
            found.append((kind, collapsed, unmarked, text.strip() != collapsed))
    return found


# Example command lines quoted in a driver's help text. Each must stay a literal
# substring of that help (so a removed example is noticed) and must parse.
DOCUMENTED_EXAMPLES = {
    "cloud_verify": [
        '--then "--suites build,corpus-compile --env TLX_JIT=0"',
        '--suites build,fuzz-campaign --fuzz-minutes 40 --max-minutes 60',
        '--bench "tlcbase --missing --collect" --bench "run --tlc --repeat 3"',
        '--bench-bin nostats=HEAD:no-stats --bench "ab --bin default=target/release/tlx '
        '--bin nostats=target/bench-bins/nostats/tlx --models ... --repeat 10"',
        # A before/after comparison on one instance: the previous revision's
        # binary built by --bench-bin, then one pass per binary (H-03 item 8;
        # the worker had to derive this combination from --bench-bin's help).
        '--bench-bin before=HEAD~1 --bench "coverage --dynamic --bin '
        'target/bench-bins/before/tlx" --bench "coverage --dynamic --bin target/release/tlx"',
        '--oracle "tlc --source external --tier medium,large -j 4 --tlc-workers 8 --timeout 10800"',
        "--suites corpus-ext-large",
    ],
}


def _flat(text):
    return " ".join(text.split())


def example_argv(driver, example):
    """Split one documented example into argv, or raise if it is not in the help."""
    text = _flat(" ".join(text for _, text in help_units(driver)))
    if _flat(example) not in text:
        raise AssertionError(f"documented example is not in {driver}.py's help text: {example!r}")
    return shlex.split(example)


def parse_example(driver, argv):
    """Parse one documented example with the driver's own parser.

    A driver that documents example command lines must expose ``parse_args(argv)``
    so the example can be run through argparse, exactly as a user would; a driver
    without that hook fails loudly here rather than documenting an unchecked
    example. ``argparse`` raises ``SystemExit`` when it refuses the combination.
    """
    module = importlib.import_module(driver)
    parse = getattr(module, "parse_args", None)
    if parse is None:
        raise AssertionError(
            f"{driver}.py documents help examples but exposes no parse_args(argv) to run them through")
    return parse(list(argv))


class DriverOptionTests(testkit.GuardedTestCase):
    def test_every_driver_option_reaches_a_consumer(self):
        for driver in DRIVERS:
            with self.subTest(driver=driver):
                orphans = orphan_options(driver)
                self.assertEqual(
                    orphans, [],
                    f"{driver}.py parses option dest(s) nothing reads: {orphans}; "
                    "give each a consumer, delete it, or put it in a mutually exclusive "
                    "group whose consumed flag the code reads")

    def test_a_driver_with_an_extracted_parser_is_still_checked(self):
        """The extraction that moved bench's parser into benchmarking/cli.py left this
        check reading an empty option set for that driver, and `orphan_options` then
        returns [] for every input: a silent pass (2026-10-09). The parser owner's
        surface must be part of the driver's, not the driver's tree alone.
        """
        dests, _, _ = _reachable_consumers("bench")
        self.assertGreater(len(dests), 50, f"bench's parser surface is not reached: {sorted(dests)}")
        flags = _driver_flags("bench")
        for flag in ("--models", "--deadline-min", "--smoke", "--measure-tlc"):
            self.assertIn(flag, flags, f"the parser owner's {flag} is not part of bench's surface")

    def test_a_handler_the_driver_holds_is_followed_but_a_dead_option_is_not(self):
        """Fail-before evidence for a pass that moved into a package module.

        The entry point dispatches through a table, so the handler is a name it
        holds rather than a call this check can follow; without the handler's body
        (what a flat ``scripts/*.py`` view sees) the option that pass reads is
        reported as an orphan, and with it only the option nothing reads is.
        """
        driver = "_handler_driver"
        handler = os.path.join("_handler_pkg", "commands", "run.py")
        TREES[driver] = ast.parse(
            "import argparse\n"
            "from _handler_pkg.commands.run import cmd_run\n"
            "def main():\n"
            "    ap = argparse.ArgumentParser()\n"
            "    ap.add_argument('--used')\n"
            "    ap.add_argument('--dead')\n"
            "    a = ap.parse_args()\n"
            "    return {'run': cmd_run}[a.cmd](a)\n")
        try:
            self.assertEqual(orphan_options(driver), ["dead", "used"],
                             "without the handler module the pass reads nothing")
            NESTED_TREES[handler] = ast.parse("def cmd_run(a):\n    return a.used\n")
            try:
                self.assertEqual(orphan_options(driver), ["dead"])
            finally:
                NESTED_TREES.pop(handler)
        finally:
            TREES.pop(driver)

    def test_package_module_import_resolves_option_consumers(self):
        driver = "_package_driver"
        module = os.path.join("_package", "budget.py")
        TREES[driver] = ast.parse(
            "import argparse\nfrom _package import budget\n"
            "ap = argparse.ArgumentParser()\nap.add_argument('--used')\n"
            "ap.add_argument('--dead')\na = ap.parse_args()\nbudget.consume(a)\n")
        try:
            self.assertEqual(orphan_options(driver), ["dead", "used"])
            NESTED_TREES[module] = ast.parse("def consume(a):\n    return a.used\n")
            self.assertEqual(orphan_options(driver), ["dead"])
        finally:
            TREES.pop(driver)
            NESTED_TREES.pop(module, None)

    def test_the_owner_map_reports_a_dead_option_in_the_owner_module(self):
        """Fail-before evidence for the owner map: an option the owner module declares
        and nothing reads is reported for the driver, exactly like one in the driver's
        own tree -- and the same driver declares no options at all without the map.
        """
        driver, owner = "_owner_driver", os.path.join("_owner_pkg", "cli.py")
        TREES[driver] = ast.parse(
            "import _owner_pkg.cli as cli\n"
            "def main():\n"
            "    parser = cli.build_parser()\n"
            "    a = parser.parse_args()\n"
            "    print(a.used)\n")
        NESTED_TREES[owner] = ast.parse(
            "import argparse\n"
            "def build_parser():\n"
            "    ap = argparse.ArgumentParser()\n"
            "    ap.add_argument('--used')\n"
            "    ap.add_argument('--dead')\n"
            "    return ap\n")
        try:
            self.assertEqual(_reachable_consumers(driver)[0], {},
                             "without the owner map this driver declares no option at all")
            PARSER_OWNERS[driver] = owner
            try:
                self.assertEqual(orphan_options(driver), ["dead"])
            finally:
                del PARSER_OWNERS[driver]
        finally:
            TREES.pop(driver)
            NESTED_TREES.pop(owner)

    def test_the_checker_follows_a_parser_namespace_pair(self):
        """Fail-before evidence: `parser, a = ap.parse_args()` binds the namespace
        exactly as `a = ap.parse_args()` does -- the entry point needs the parser back
        to report a refusal -- and reading `a.used` must count as a consumer. Without
        the pair target, every option of such a driver looks unread.
        """
        source = ("import argparse\n"
                  "def main():\n"
                  "    ap = argparse.ArgumentParser()\n"
                  "    ap.add_argument('--used')\n"
                  "    ap.add_argument('--dead')\n"
                  "    parser, a = ap.parse_args()\n"
                  "    print(a.used)\n")
        tree = ast.parse(source)
        saved = TREES.get("_synthetic_pair")
        try:
            TREES["_synthetic_pair"] = tree
            self.assertEqual(_namespaces(tree), {"parser", "a"})
            dests, consumed, _ = _reachable_consumers("_synthetic_pair")
            self.assertEqual(sorted(dests), ["dead", "used"])
            self.assertEqual(sorted(set(dests) - consumed), ["dead"])
        finally:
            if saved is None:
                del TREES["_synthetic_pair"]
            else:
                TREES["_synthetic_pair"] = saved

    def test_the_checker_reports_a_dead_option(self):
        """Fail-before evidence: a synthetic driver with an unread option is caught."""
        source = ("import argparse\n"
                  "def main():\n"
                  "    ap = argparse.ArgumentParser()\n"
                  "    ap.add_argument('--used')\n"
                  "    ap.add_argument('--dead')\n"
                  "    a = ap.parse_args()\n"
                  "    print(a.used)\n")
        tree = ast.parse(source)
        saved = TREES.get("_synthetic")
        try:
            TREES["_synthetic"] = tree
            dests, consumed, _ = _reachable_consumers("_synthetic")
            self.assertEqual(sorted(dests), ["dead", "used"])
            self.assertEqual(sorted(set(dests) - consumed), ["dead"])
        finally:
            if saved is None:
                del TREES["_synthetic"]
            else:
                TREES["_synthetic"] = saved

    def test_help_does_not_promise_a_refused_combination(self):
        """No help unit may offer a combination the driver's own parser refuses."""
        for driver in DRIVERS:
            with self.subTest(driver=driver):
                found = undocumented_refusals(driver)
                self.assertEqual(
                    found, [],
                    f"{driver}.py's help promises a refused option combination: "
                    + "; ".join(f"[{kind}] {text!r} names {pairs}"
                                + (" (the help unit is wrapped across lines)" if wrapped else "")
                                for kind, text, pairs, wrapped in found)
                    + " -- reword the help (or the refusal), keeping the two options marked as alternatives")

    def test_a_refusal_wrapped_between_two_options_is_still_recognized(self):
        """Fail-before evidence: the alternatives match is whitespace-insensitive.

        The pair here is stated as one sentence wrapped inside the sentence -
        `--alpha and --gamma cannot be\\ncombined with --beta` - which a literal
        match read as the help promising that combination and reported, so a
        re-wrap of a *correct* help unit failed the check (H-03 item 3).
        """
        source = (
            '"""Tool (--alpha, --beta, --gamma).\n'
            '\n'
            '--alpha given with --beta is refused; --alpha and --gamma cannot be\n'
            'combined with --beta (run --alpha in a second invocation).\n'
            '"""\n'
            "import argparse\n"
            "def main():\n"
            "    ap = argparse.ArgumentParser()\n"
            "    ap.add_argument('--alpha')\n"
            "    ap.add_argument('--beta')\n"
            "    ap.add_argument('--gamma')\n"
            "    a = ap.parse_args()\n"
            "    if a.alpha and a.beta:\n"
            "        ap.error('--alpha cannot be combined with --beta')\n"
            "    if a.gamma and a.beta:\n"
            "        ap.error('--gamma cannot be combined with --beta')\n"
            "    print(a.alpha, a.beta, a.gamma)\n"
        )
        saved = TREES.get("_synthetic_wrapped")
        try:
            TREES["_synthetic_wrapped"] = ast.parse(source)
            self.assertEqual(undocumented_refusals("_synthetic_wrapped"), [],
                             "a wrapped refusal names both options as alternatives")
        finally:
            if saved is None:
                TREES.pop("_synthetic_wrapped", None)
            else:
                TREES["_synthetic_wrapped"] = saved

    def test_a_reported_refusal_says_the_unit_is_wrapped(self):
        """The reader of a finding sees that the text spans lines."""
        source = (
            '"""Tool (--alpha, --beta, --gamma).\n'
            '\n'
            '--alpha given with --beta is refused; run --alpha in a second\n'
            'invocation, or as a --gamma pass.\n'
            '"""\n'
            "import argparse\n"
            "def main():\n"
            "    ap = argparse.ArgumentParser()\n"
            "    ap.add_argument('--alpha')\n"
            "    ap.add_argument('--beta')\n"
            "    ap.add_argument('--gamma')\n"
            "    a = ap.parse_args()\n"
            "    if a.alpha and a.beta:\n"
            "        ap.error('--alpha cannot be combined with --beta')\n"
            "    if a.gamma and a.beta:\n"
            "        ap.error('--gamma cannot be combined with --beta')\n"
            "    print(a.alpha, a.beta, a.gamma)\n"
        )
        saved = TREES.get("_synthetic_wrapped_report")
        try:
            TREES["_synthetic_wrapped_report"] = ast.parse(source)
            found = undocumented_refusals("_synthetic_wrapped_report")
            self.assertEqual(len(found), 1, found)
            kind, text, pairs, wrapped = found[0]
            self.assertTrue(wrapped, "the unit is one paragraph of two lines")
            self.assertNotIn("\n", text, "the reported text is collapsed into one line")
            self.assertEqual(pairs, [("--beta", "--gamma")])
        finally:
            if saved is None:
                TREES.pop("_synthetic_wrapped_report", None)
            else:
                TREES["_synthetic_wrapped_report"] = saved

    def test_the_help_checker_catches_a_promised_refusal(self):
        """Fail-before evidence: a help unit that promises a refused pair is caught."""
        source = (
            '"""Tool (--alpha, --beta, --gamma).\n'
            '\n'
            '--alpha given with --beta is refused; run --alpha in a second invocation, or as a --gamma pass.\n'
            '"""\n'
            "import argparse\n"
            "def main():\n"
            "    ap = argparse.ArgumentParser()\n"
            "    ap.add_argument('--alpha')\n"
            "    ap.add_argument('--beta')\n"
            "    ap.add_argument('--gamma')\n"
            "    a = ap.parse_args()\n"
            "    if a.alpha and a.beta:\n"
            "        ap.error('--alpha cannot be combined with --beta')\n"
            "    if a.gamma and a.beta:\n"
            "        ap.error('--gamma cannot be combined with --beta')\n"
            "    print(a.alpha, a.beta, a.gamma)\n"
        )
        saved = TREES.get("_synthetic_help")
        try:
            TREES["_synthetic_help"] = ast.parse(source)
            found = undocumented_refusals("_synthetic_help")
            self.assertEqual([pairs for _, _, pairs, _ in found], [[("--beta", "--gamma")]],
                             "the marker ('refused') and the unmarked pair --beta/--gamma must be reported")
        finally:
            if saved is None:
                TREES.pop("_synthetic_help", None)
            else:
                TREES["_synthetic_help"] = saved

    def test_documented_example_commands_parse(self):
        """Every example command line in a driver's help must parse with argparse."""
        for driver, examples in DOCUMENTED_EXAMPLES.items():
            for example in examples:
                with self.subTest(driver=driver, example=example):
                    argv = example_argv(driver, example)
                    try:
                        parse_example(driver, argv)
                    except SystemExit as error:
                        self.fail(f"{driver}.py documents {example!r} but its parser refuses it "
                                  f"(SystemExit {error.code})")

    def test_the_example_checker_catches_a_refused_example(self):
        """Fail-before evidence: a documented example the parser refuses fails the check."""
        argv = example_argv("cloud_verify", DOCUMENTED_EXAMPLES["cloud_verify"][0])
        self.assertEqual(argv[:1], ["--then"])
        with self.assertRaises(SystemExit):
            # The very combination the stale help once offered alongside --bench.
            parse_example("cloud_verify", ["--bench", "table", "--then", "--suites", "build"])


if __name__ == "__main__":
    unittest.main()
