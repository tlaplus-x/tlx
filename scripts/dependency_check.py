#!/usr/bin/env python3
"""Cargo dependency-direction and feature-closure policy for the workspace.

Normal dependency edges are declared explicitly (ARCH-01): a lower layer must
not start importing a higher one by accident, so an edge nobody listed is a
violation, and a listed edge that no longer exists is a stale entry that would
quietly authorize the next one. Cycles are allowed only through dev-only
harness edges (tlx-testkit), never through production ones.

Feature configurations are checked per package, not on the workspace union
(ARCH-04/ARCH-05): the whole workspace turns the JIT on through tlx-cli, so
only a package-focused closure can show that a fixture which claims not to
need Cranelift, or the compiler, really does not get it. Each closure names
what must be absent and what must be present, so the absence assertion cannot
be satisfied by a resolution that finds nothing at all; the closure assertions
in turn rest on `#[cfg(feature = ...)]` selecting real code, which the
known-bad compile-error probe at the end of this file proves directly.

usage:
  scripts/dependency_check.py [--root DIR] [--quiet]

Exit 0 when every check passes, 1 with one line per violation.
"""
import argparse
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TIMEOUT = 300

#: Every workspace-internal edge of the production graph, as
#: ``(consumer, dependency)``. Optional dependencies of a workspace member are
#: listed in OPTIONAL_EDGES: they exist only when a declared feature turns
#: them on, but they are still normal edges for direction and cycle purposes.
NORMAL_EDGES = frozenset({
    ("tlx", "tlx-base"),
    ("tlx", "tlx-compile"),
    ("tlx", "tlx-eval"),
    ("tlx", "tlx-front"),
    ("tlx", "tlx-live"),
    ("tlx", "tlx-runtime"),
    ("tlx", "tlx-sema"),
    ("tlx", "tlx-value"),
    ("tlx-native", "tlx-base"),
    ("tlx-native", "tlx-value"),
    ("tlx-compile", "tlx-base"),
    ("tlx-compile", "tlx-native"),
    ("tlx-compile", "tlx-eval"),
    ("tlx-compile", "tlx-front"),
    ("tlx-compile", "tlx-layout"),
    ("tlx-compile", "tlx-runtime"),
    ("tlx-compile", "tlx-sema"),
    ("tlx-compile", "tlx-value"),
    ("tlx-eval", "tlx-base"),
    ("tlx-eval", "tlx-front"),
    ("tlx-eval", "tlx-live"),
    ("tlx-eval", "tlx-runtime"),
    ("tlx-eval", "tlx-sema"),
    ("tlx-eval", "tlx-value"),
    ("tlx-layout", "tlx-base"),
    ("tlx-layout", "tlx-value"),
    ("tlx-live", "tlx-base"),
    ("tlx-runtime", "tlx-base"),
    ("tlx-runtime", "tlx-live"),
    ("tlx-runtime", "tlx-value"),
    ("tlx-sema", "tlx-front"),
    ("tlx-testkit", "tlx-base"),
    ("tlx-value", "tlx-base"),
})

#: Optional dependencies of one workspace member on another: pure dev-side
#: wiring, off unless the forwarding feature names them.
OPTIONAL_EDGES = frozenset({
    ("tlx-testkit", "tlx-native"),
    ("tlx-testkit", "tlx-compile"),
    ("tlx-testkit", "tlx-eval"),
    ("tlx-testkit", "tlx-front"),
    ("tlx-testkit", "tlx-layout"),
    ("tlx-testkit", "tlx-runtime"),
    ("tlx-testkit", "tlx-sema"),
    ("tlx-testkit", "tlx-value"),
})

#: Dev-only edges (the test harness). Every cycle of the combined graph must
#: run through at least one of these.
DEV_EDGES = frozenset({
    ("tlx", "tlx-testkit"),
    ("tlx-native", "tlx-runtime"),
    ("tlx-compile", "tlx-testkit"),
    ("tlx-eval", "tlx-testkit"),
    ("tlx-front", "tlx-testkit"),
    ("tlx-layout", "tlx-testkit"),
    ("tlx-live", "tlx-testkit"),
    ("tlx-runtime", "tlx-testkit"),
    ("tlx-sema", "tlx-testkit"),
    ("tlx-value", "tlx-testkit"),
})

EDGE_KINDS = {"normal": NORMAL_EDGES, "optional": OPTIONAL_EDGES, "dev": DEV_EDGES}

#: One `cargo tree` configuration per assertion. `forbidden`/`required` are
#: name prefixes; `cranelift` therefore matches every Cranelift crate without
#: listing the five backends (ARCH-04, F11).
CLOSURES = (
    {"name": "cli-jit-off", "package": "tlx", "features": (), "no_default": True,
     "edges": "normal,build", "forbidden": ("cranelift",), "required": ()},
    {"name": "cli-jit-on", "package": "tlx", "features": (), "no_default": False,
     "edges": "normal,build", "forbidden": (), "required": ("cranelift-codegen",)},
    {"name": "testkit-basic", "package": "tlx-testkit", "features": (), "no_default": True,
     "edges": "normal", "required": ("tlx-base",),
     "forbidden": ("cranelift", "tlx-layout", "tlx-value", "tlx-front", "tlx-sema", "tlx-eval",
                   "tlx-runtime", "tlx-compile", "tlx-native")},
    {"name": "testkit-values", "package": "tlx-testkit", "features": ("values",), "no_default": True,
     "edges": "normal", "required": ("tlx-layout", "tlx-value"),
     "forbidden": ("cranelift", "tlx-front", "tlx-sema", "tlx-eval", "tlx-runtime",
                   "tlx-compile", "tlx-native")},
    {"name": "testkit-interpreted", "package": "tlx-testkit", "features": ("interpreted",), "no_default": True,
     "edges": "normal", "required": ("tlx-eval",),
     "forbidden": ("cranelift", "tlx-compile", "tlx-native")},
    {"name": "testkit-compiled", "package": "tlx-testkit", "features": ("compiled",), "no_default": True,
     "edges": "normal", "required": ("tlx-compile", "tlx-native"),
     "forbidden": ("cranelift",)},
    {"name": "testkit-jit", "package": "tlx-testkit", "features": ("jit",), "no_default": True,
     "edges": "normal", "forbidden": (), "required": ("cranelift-codegen",)},
    {"name": "layout-dev", "package": "tlx-layout", "features": (), "no_default": False,
     "edges": "normal,dev", "forbidden": ("cranelift", "tlx-compile", "tlx-native", "tlx-eval",
                                          "tlx-runtime"),
     "required": ("tlx-testkit",)},
)

#: The known-bad source of the cfg probe: it cannot compile when the `jit`
#: cfg is set, so a *successful* compile proves the branch was not reached and
#: a *failed* one proves it was. Both directions are required, or an absence
#: assertion built on `#[cfg]` could rest on a cfg that selects nothing.
PROBE_SOURCE = """\
#[cfg(feature = "jit")]
compile_error!("dependency_check probe: the feature = \\"jit\\" branch was compiled");
"""
PROBE_MARKER = "dependency_check probe"


def run_command(args, cwd=None, env=None):
    """Run a command, capturing text output (the seam tests replace)."""
    return subprocess.run([str(a) for a in args], cwd=cwd, env=env,
                          capture_output=True, text=True, timeout=TIMEOUT)


def last_line(text):
    """The last non-empty line of a command's output, for a one-line problem."""
    lines = [line.strip() for line in (text or "").splitlines() if line.strip()]
    return lines[-1] if lines else "(no output)"


def cargo_metadata(root):
    """The workspace members and their declared dependencies (no resolution)."""
    return json.loads(run_command(["cargo", "metadata", "--no-deps", "--format-version", "1",
                                   "--offline"], cwd=root).stdout)


def package_kinds(dependency):
    """The dependency-kind list of one metadata entry (`null` means normal)."""
    kind = dependency.get("kind")
    if kind is None:
        return [None]
    if isinstance(kind, str):
        return [kind]
    return list(kind)


def feature_forwarding(package):
    """The dependency names a package's feature table enables, and by which feature.

    ``dep:name``, ``name/feature`` and a feature named exactly like the
    optional dependency are the three ways a manifest turns one on.
    """
    forwarded = {}
    for feature, items in package.get("features", {}).items():
        forwarded.setdefault(feature, [])
        for item in items:
            if item.startswith("dep:"):
                forwarded.setdefault(item[len("dep:"):], []).append(feature)
            elif "/" in item:
                forwarded.setdefault(item.split("/", 1)[0], []).append(feature)
    return forwarded


def workspace_packages(metadata):
    """``{name: package}`` for the members a metadata document describes."""
    ids = set(metadata.get("workspace_members") or ())
    return {p["name"]: p for p in metadata.get("packages", ()) if not ids or p["id"] in ids}


def declared_edges(packages):
    """``{(consumer, dependency): kind}`` for the workspace-internal edges.

    A manifest that names the same package as both a normal and a dev
    dependency yields one edge, classified by its most binding use.
    """
    rank = {"dev": 0, "optional": 1, "normal": 2}
    edges = {}
    for name, package in packages.items():
        for dependency in package.get("dependencies", ()):
            if dependency["name"] not in packages:
                continue
            kinds = package_kinds(dependency)
            if "dev" in kinds:
                kind = "dev"
            elif dependency.get("optional"):
                kind = "optional"
            else:
                kind = "normal"
            key = (name, dependency["name"])
            if key not in edges or rank[kind] > rank[edges[key]]:
                edges[key] = kind
    return edges


def edge_problems(edges):
    """Undeclared and stale workspace-internal edges (ARCH-01)."""
    problems = []
    for edge, kind in sorted(edges.items()):
        if edge not in EDGE_KINDS[kind]:
            other = [k for k, allowed in EDGE_KINDS.items() if edge in allowed]
            hint = f" (it is declared as {other[0]})" if other else ""
            problems.append(f"undeclared {kind} dependency edge {edge[0]} -> {edge[1]}{hint}: "
                            f"declare it in {kind.upper()}_EDGES in scripts/dependency_check.py if it is "
                            f"deliberate (ARCH-01)")
    for kind, allowed in sorted(EDGE_KINDS.items()):
        for edge in sorted(allowed - set(edges)):
            problems.append(f"stale {kind} dependency edge {edge[0]} -> {edge[1]}: it no longer exists, "
                            f"remove it from {kind.upper()}_EDGES so a later edge there is a change "
                            f"(ARCH-01)")
    return problems


def cycles(graph):
    """The cycles a depth-first walk closes, as paths (`{node: {successor}}`)."""
    found = set()
    stack = []
    seen = set()

    def walk(node):
        stack.append(node)
        seen.add(node)
        for successor in sorted(graph.get(node, ())):
            if successor in stack:
                found.add(tuple(stack[stack.index(successor):] + [successor]))
            elif successor not in seen:
                walk(successor)
        stack.pop()

    for node in sorted(graph):
        if node not in seen:
            walk(node)
    return sorted(found)


def cycle_problems(edges):
    """Only the production edges must be acyclic; dev edges may close loops.

    The test harness sits above every crate, so its dev edges legitimately
    close cycles through the graph; a cycle that contains no dev edge is
    exactly a cycle of the production subgraph, which is why this walks that
    subgraph rather than filtering cycles out of the whole graph. The filter
    was the first version and it was wrong: the path a walk closes runs from
    the successor it re-enters to wherever it reached that successor, so a
    dev detour can put a dev edge into the report of a production cycle -
    `a -> c -> a` plus the dev edges `a -> b`, `b -> c` would print as
    `a -> b -> c -> a` and be waved through (ARCH-01).
    """
    production = {}
    for (consumer, dependency), kind in edges.items():
        if kind != "dev":
            production.setdefault(consumer, set()).add(dependency)
    return ["dependency cycle without a dev edge: " + " -> ".join(cycle) +
            "; production edges must be acyclic (ARCH-01)" for cycle in cycles(production)]


def feature_problems(packages):
    """Feature forwarding: optional dependencies and inherited defaults (ARCH-04)."""
    problems = []
    for name, package in sorted(packages.items()):
        forwarded = feature_forwarding(package)
        for dependency in package.get("dependencies", ()):
            local = dependency.get("rename") or dependency["name"]
            if dependency.get("optional") and local not in forwarded:
                problems.append(f"{name}: optional dependency {local} is not named by any feature: "
                                f"forward it as dep:{local} or {local}/<feature> (ARCH-04)")
        for dependency in package.get("dependencies", ()):
            if not dependency.get("uses_default_features"):
                continue
            target = packages.get(dependency["name"])
            defaults = target and target.get("features", {}).get("default")
            if defaults:
                problems.append(f"{name}: takes {dependency['name']} with its default features on "
                                f"({', '.join(defaults)}): disable them at the consumer and forward "
                                f"explicitly, or the workspace union turns them on everywhere (ARCH-04)")
    return problems


def closure_command(config):
    """The ``cargo tree`` argv of one closure assertion."""
    command = ["cargo", "tree", "-p", config["package"], "--offline", "--prefix", "none",
               "--format", "{p}", "-e", config["edges"]]
    if config["no_default"]:
        command.append("--no-default-features")
    if config["features"]:
        command += ["--features", ",".join(config["features"])]
    return command


def tree_packages(output):
    """The package names of a ``--format {p}`` tree, in order."""
    names = []
    for line in output.splitlines():
        line = line.strip()
        if line and not line.startswith("warning:"):
            names.append(line.split(" ", 1)[0])
    return names


def matches(name, prefix):
    """A closure entry matches a package name or a family of them."""
    return name == prefix or name.startswith(prefix + "-")


def closure_problems(configs, root):
    """Absence and presence of the intended feature closure, per package."""
    problems = []
    for config in configs:
        result = run_command(closure_command(config), cwd=root)
        if result.returncode != 0:
            problems.append(f"closure {config['name']}: `{' '.join(closure_command(config))}` failed "
                            f"(exit {result.returncode}): {last_line(result.stderr)}")
            continue
        names = tree_packages(result.stdout)
        for prefix in config["forbidden"]:
            present = sorted({n for n in names if matches(n, prefix)})
            if present:
                problems.append(f"closure {config['name']}: {config['package']} still reaches "
                                f"{', '.join(present)} with"
                                f"{' no default features' if config['no_default'] else ' the default features'}"
                                f"{' + ' + ','.join(config['features']) if config['features'] else ''}"
                                f" (ARCH-04/ARCH-05)")
        for prefix in config["required"]:
            if not any(matches(n, prefix) for n in names):
                problems.append(f"closure {config['name']}: {config['package']} does not reach {prefix}, "
                                f"so the absence assertions of this configuration prove nothing (ARCH-04)")
    return problems


def probe_problems(root):
    """Prove that a `#[cfg(feature = ...)]` branch is compiled when it is set.

    The probe is known-bad by construction: the `jit` branch holds a
    `compile_error!`. Compiling it without the cfg must succeed (nothing is
    selected) and with `--cfg feature="jit"` must fail on that very message
    (the branch was compiled). Anything else means the feature mechanism the
    closure assertions rely on is not doing what they assume.
    """
    rustc = os.environ.get("RUSTC") or "rustc"
    cfg = ["--cfg", 'feature="jit"']
    problems = []
    with tempfile.TemporaryDirectory(prefix="tlx-cfg-probe.") as directory:
        source = Path(directory) / "probe.rs"
        source.write_text(PROBE_SOURCE)
        base = [rustc, "--crate-type=lib", "--edition=2021", "--emit=metadata", "--out-dir", directory]

        def compile_with(extra):
            try:
                return run_command(base + extra + [str(source)], cwd=root)
            except OSError as error:
                return error

        off, on = compile_with([]), compile_with(cfg)
        for result, label in ((off, "without the cfg"), (on, "with the cfg")):
            if isinstance(result, OSError):
                return [f"cfg probe: cannot run {rustc} ({result}); the JIT cfg branch is unproven "
                        f"(ARCH-04)"]
            if result.returncode == 0 and label == "with the cfg":
                problems.append('cfg probe: --cfg \'feature="jit"\' did not compile the jit branch, so '
                                'the closure assertions of this file assume a cfg that selects nothing '
                                '(ARCH-04)')
            elif result.returncode != 0 and label == "without the cfg":
                problems.append(f"cfg probe: the known-bad probe fails even without the cfg "
                                f"({last_line(result.stderr)}), so a successful compile would prove "
                                f"nothing (ARCH-04)")
            elif result.returncode != 0 and PROBE_MARKER not in result.stderr:
                problems.append(f"cfg probe: {label} the probe failed for an unrelated reason: "
                                f"{last_line(result.stderr)} (ARCH-04)")
    return problems


def check(root=ROOT):
    """Every violation of the dependency and feature policy of `root`."""
    packages = workspace_packages(cargo_metadata(root))
    edges = declared_edges(packages)
    problems = edge_problems(edges)
    problems += cycle_problems(edges)
    problems += feature_problems(packages)
    problems += closure_problems(CLOSURES, root)
    problems += probe_problems(root)
    return problems


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--root", default=str(ROOT), help=f"checkout root (default: {ROOT})")
    parser.add_argument("--quiet", action="store_true", help="print only violations")
    arguments = parser.parse_args(argv)
    problems = check(Path(arguments.root))
    for problem in problems:
        print(f"dependency policy: {problem}")
    if not arguments.quiet:
        print(f"dependency policy: {len(NORMAL_EDGES) + len(OPTIONAL_EDGES)} normal and "
              f"{len(DEV_EDGES)} dev edges, {len(CLOSURES)} feature closures, 1 cfg probe; "
              f"{len(problems)} problem(s)")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
