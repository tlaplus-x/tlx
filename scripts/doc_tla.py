"""Validate fenced TLA+ documentation without evaluating a model."""
from pathlib import Path
import re
import subprocess

import tempdirs


def blocks(text):
    fence = None
    start = 0
    body = []
    for line_number, line in enumerate(text.splitlines(), 1):
        if fence is None:
            match = re.match(r'^\s*(`{3,}|~{3,})\s*tla\s*$', line)
            if match:
                fence, start, body = match.group(1), line_number + 1, []
        elif re.match(r'^\s*' + re.escape(fence[0]) + '{' + str(len(fence)) + r',}\s*$', line):
            yield start, '\n'.join(body) + '\n'
            fence = None
        else:
            body.append(line)


def check_files(paths, root='.', binary=None, runner=subprocess.run, note=print):
    root = Path(root).resolve()
    if binary is None:
        binary = root / 'target/test-release/tlx'
    binary = Path(binary).resolve()
    available = binary.is_file()
    stale = False
    if available:
        # A binary built before `tlx parse` existed (doccheck runs before the gate's build)
        # cannot judge documentation: probe it once with a trivial module.
        with tempdirs.TemporaryDirectory(prefix='tlx-doccheck-', owner_root=root) as directory:
            probe = Path(directory) / 'Probe.tla'
            probe.write_text('---- MODULE Probe ----\n====\n')
            try:
                stale = runner([str(binary), 'parse', str(probe)], capture_output=True, text=True,
                               timeout=30).returncode != 0
            except (OSError, subprocess.TimeoutExpired):
                stale = True
        available = not stale
    skipped = 0
    problems = []
    for path in paths:
        for start, source in blocks(Path(path).read_text()):
            for offset, line in enumerate(source.splitlines()):
                if '\\|' in line:
                    problems.append(f'{path}:{start + offset}: Markdown table escape \\| in TLA+ code block')
            module = re.search(r'^\s*-{4,}\s*MODULE\s+(\w+)', source, re.M)
            if not module:
                continue
            if not available:
                skipped += 1
                continue
            with tempdirs.TemporaryDirectory(prefix='tlx-doccheck-', owner_root=root) as directory:
                spec = Path(directory) / (module.group(1) + '.tla')
                spec.write_text(source)
                try:
                    result = runner([str(binary), 'parse', str(spec)], capture_output=True, text=True, timeout=30)
                except (OSError, subprocess.TimeoutExpired) as error:
                    problems.append(f'{path}:{start}: TLA+ parse-only check failed: {error}')
                    continue
                if result.returncode:
                    detail = (result.stderr or result.stdout).strip()
                    # Map front-end source positions back into the Markdown document.
                    detail = re.sub(re.escape(str(spec)) + r':(\d+):',
                                    lambda m: f'{path}:{start + int(m.group(1)) - 1}:', detail)
                    problems.append(f'{path}:{start}: invalid TLA+ module: {detail}')
    if skipped:
        why = 'cannot parse a trivial module (built before `tlx parse`?)' if stale else 'missing'
        note(f'TLA+ module parsing skipped ({skipped} blocks): {binary} {why}; '
             'build with cargo build --profile test-release -p tlx')
    return problems
