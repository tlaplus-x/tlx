#!/usr/bin/env python3
"""Check tlx docs: links, § references, TLX_* names, file paths, stale terms.

Usage (from the repository root): python3 scripts/doccheck.py [ROOT] [--require-examples]

Checks README, AGENTS, CONTRIBUTING, docs, tracked skills and public bench Markdown.
By default missing example-parsing prerequisites are reported as skips; --require-examples
rejects them. Example validation is parse-only, never model execution.
Process documents live in the untracked work/ directory and are not checked; § references to them
(architecture-review.md, code-health.md, plan.md) are skipped.
A code line containing the marker `doccheck: ignore` is skipped (fixture paths a test writes into a temporary repository).
AGENTS.md and the current benchmark inputs and evidence are public. Local development
configuration and archived process documents are excluded from the published tree.
An absent document is named and skipped; a link to a missing file is always broken.
Exit status: 0 for "0 problems", 1 when any problem is reported.
"""
import argparse
import glob
import os
import re
import sys
import subprocess
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('root', nargs='?', default='.')
parser.add_argument('--require-examples', action='store_true',
                    help='fail if complete TLA+ modules cannot be parsed; does not run models')
args = parser.parse_args()
os.chdir(args.root)


#: Documents a checkout of this tree is expected to carry; each is checked when
#: it is here. Partial checkouts report missing documents explicitly.
PUBLISHED_DOCS = ('README.md', 'AGENTS.md')


def current_docs():
    out = [p for p in PUBLISHED_DOCS if os.path.isfile(p)]
    for name in ('CONTRIBUTING.md', 'SECURITY.md'):
        if os.path.isfile(name):
            out.append(name)
    for p in sorted(glob.glob('docs/**/*.md', recursive=True)):
        out.append(p)
    tracked = subprocess.run(['git', 'ls-files', '-z', '--', '.agents/skills', 'bench'],
                             capture_output=True, text=True)
    # Standalone source archives have no index; check all their Markdown instead.
    extra = (tracked.stdout.split('\0') if tracked.returncode == 0 else
             glob.glob('.agents/skills/**/*.md', recursive=True) + glob.glob('bench/**/*.md', recursive=True))
    out.extend(sorted(p for p in extra if p.endswith('.md') and os.path.isfile(p)))
    return out


def prose_lines(text):
    """Preserve source line numbers outside CommonMark backtick/tilde fences."""
    fence = None
    for number, line in enumerate(text.splitlines(), 1):
        if fence:
            if re.match(r'^ {0,3}' + re.escape(fence[0]) + '{' + str(len(fence)) + r',}\s*$', line):
                fence = None
            continue
        match = re.match(r'^ {0,3}(`{3,}|~{3,})(.*)$', line)
        if match and (match[1][0] == '~' or '`' not in match[2]):
            fence = match[1]
            continue
        yield number, line


NUM_HEAD = re.compile(r'^(#{1,6})\s+(?:[A-Z]{1,3}\s*)?§?(\d+(?:\.\d+)*)(?:[.\s:：、）)]|$)')
_sec_cache = {}


def sections(path):
    if path in _sec_cache:
        return _sec_cache[path]
    secs = set()
    try:
        text = Path(path).read_text(encoding='utf-8')
    except FileNotFoundError:
        return None
    for _, line in prose_lines(text):
        m = NUM_HEAD.match(line)
        if m:
            secs.add(m.group(2))
        m2 = re.match(r'^#{1,6}\s+(\d+)-(\d+)\.', line)
        if m2:
            for k in range(int(m2.group(1)), int(m2.group(2)) + 1):
                secs.add(str(k))
    _sec_cache[path] = secs
    return secs


def anchors(path):
    text = Path(path).read_text(encoding='utf-8')
    out = set()
    for _, line in prose_lines(text):
        out.update(re.findall(r'<a\s+(?:id|name)=["\']([^"\']+)["\']', line, re.I))
        m = re.match(r'^#{1,6}\s+(.*)$', line)
        if m:
            h = re.sub(r'\s+#+\s*$', '', m.group(1)).strip().lower()
            h = re.sub(r'[^\w\- ]', '', h).replace(' ', '-')
            unique, suffix = h, 0
            while unique in out:
                suffix += 1
                unique = f'{h}-{suffix}'
            out.add(unique)
    return out


DOCNAMES = {}
for p in glob.glob('docs/**/*.md', recursive=True):
    DOCNAMES.setdefault(os.path.basename(p), []).append(p)


def resolve_doc(name, ctx):
    if name.startswith('docs/'):
        return name if os.path.exists(name) else None
    p = os.path.normpath(os.path.join(os.path.dirname(ctx), name))
    if os.path.exists(p):
        return p
    if os.path.exists(os.path.join('docs', name)):
        return os.path.join('docs', name)
    base = os.path.basename(name)
    c = DOCNAMES.get(base, [])
    return sorted(c)[0] if c else None


STEMS = 'design|usage|configuration|testing|compat|features|scale|mixed-mode|unsafe-audit|tlc-semantics'
SECREF = re.compile(r'((?:docs/)?(?:notes/)?(?:[A-Za-z0-9_.-]+\.md|(?:' + STEMS + r')(?![\w.-])))?\s?(?:的\s?)?§\s?(\d+(?:\.\d+)*)((?:\s?(?:[–/-]|[、,，和与]\s?§)\s?§?\s?\d+(?:\.\d+)*)*)')
# Process documents live in the untracked work/ directory (not checked).
WORK_DOCS = ('plan.md', 'architecture-review.md', 'code-health.md')
CODEREF = re.compile(r'((?:docs/)?(?:notes/)?[A-Za-z0-9_-]+\.md)\s?§\s?(\d+(?:\.\d+)*)((?:\s?(?:[–-]|,\s?§)\s?\d+(?:\.\d+)*)*)')
LINK = re.compile(r'\[[^\]]*\]\(([^)\s]+)\)')
DOCPATH = re.compile(r'(?<![\w/])(docs/[A-Za-z0-9_./-]+?\.(?:md|py|json))')

problems = []
IGNORE_MARK = 'doccheck: ' + 'ignore'


def check_doc(path, links_only=False):
    text = Path(path).read_text(encoding='utf-8', errors='replace')
    own = sections(path)
    for ln, line in prose_lines(text):
        for m in LINK.finditer(line):
            t = m.group(1)
            if re.match(r'^[a-z]+://', t) or t.startswith('mailto:'):
                continue
            f, _, anc = t.partition('#')
            tgt = path if not f else os.path.normpath(os.path.join(os.path.dirname(path), f))
            if not os.path.exists(tgt):
                problems.append(f'{path}:{ln}: broken link {t}')
            elif anc and tgt.endswith('.md') and anc not in anchors(tgt):
                problems.append(f'{path}:{ln}: missing anchor {t}')
        if links_only:
            continue
        for m in SECREF.finditer(line):
            doc = m.group(1)
            nums = [m.group(2)] + re.findall(r'\d+(?:\.\d+)*', m.group(3) or '')
            if doc:
                if os.path.basename(doc) in WORK_DOCS:
                    continue
                if not doc.endswith('.md'):
                    doc += '.md'
                tgt = resolve_doc(doc, path)
                if tgt is None:
                    problems.append(f'{path}:{ln}: § ref to unknown doc {doc}')
                    continue
                secs = sections(tgt)
            else:
                tgt, secs = path, own
            for n in nums:
                if n not in secs:
                    problems.append(f'{path}:{ln}: {os.path.basename(tgt)} has no §{n}  [{line.strip()[:100]}]')
        for m in DOCPATH.finditer(line):
            if not os.path.exists(m.group(1)):
                problems.append(f'{path}:{ln}: missing path {m.group(1)}')


def check_standards(path='docs/development-standards.md'):
    """The stable rule catalog is an ordered bijection between index and bodies."""
    expected = [f'{area}-{n:02}' for area, count in
                [('CODE', 24), ('DOC', 12), ('HARNESS', 22), ('ARCH', 10)]
                for n in range(1, count + 1)]

    def fail(detail):
        problems.append(f'{path}: standards schema: {detail}')

    if not os.path.isfile(path):
        fail('missing standard')
        return
    text = '\n'.join(line for _, line in prose_lines(Path(path).read_text(encoding='utf-8')))
    headings = list(re.finditer(r'^### ([A-Z]+-\d+)\s*$', text, re.M))
    ids = [m[1] for m in headings]
    if ids != expected:
        fail('rule headings must contain all 68 unique ordered IDs')
    index_section = re.search(r'^## Rule index\s*\n(.*?)(?=^## |\Z)', text, re.M | re.S)
    index = re.findall(r'^\| \[([A-Z]+-\d+)\]\(#([\w-]+)\) \| ([^|]+) \| (\w+) \|\s*$',
                       index_section[1] if index_section else '', re.M)
    if [row[0] for row in index] != expected:
        fail('index must contain all 68 unique ordered IDs')
    for rule, anchor, title, area in index:
        if anchor != rule.lower() or area != rule.split('-')[0] or not title.strip():
            fail(f'{rule}: invalid index anchor, criterion or area')
    for i, heading in enumerate(headings):
        end = headings[i + 1].start() if i + 1 < len(headings) else len(text)
        body = text[heading.end():end]
        fields = re.findall(r'^- \*\*([^*]+):\*\*([^\n]*)', body, re.M)
        if [name for name, _ in fields] != ['Rule', 'Rationale', 'Checked by', 'Example']:
            fail(f'{heading[1]}: requires exactly Rule, Rationale, Checked by, Example fields')
        elif any(not value.strip() for _, value in fields):
            fail(f'{heading[1]}: empty field')
    print(f'standards schema: {len(ids)} rules checked')


def check_code(p):
    text = Path(p).read_text(encoding='utf-8', errors='replace')
    for ln, line in enumerate(text.splitlines(), 1):
        if IGNORE_MARK in line:
            continue
        for m in CODEREF.finditer(line):
            if os.path.basename(m.group(1)) in WORK_DOCS or 'SKILL' in m.group(1):
                continue
            tgt = resolve_doc(m.group(1), os.path.join('docs', 'x.md'))
            if tgt is None:
                problems.append(f'{p}:{ln}: unknown doc {m.group(1)}')
                continue
            secs = sections(tgt)
            for n in [m.group(2)] + re.findall(r'\d+(?:\.\d+)*', m.group(3) or ''):
                if n not in secs:
                    problems.append(f'{p}:{ln}: {tgt} has no §{n}')
        for m in DOCPATH.finditer(line):
            if not os.path.exists(m.group(1)):
                problems.append(f'{p}:{ln}: missing path {m.group(1)}')


docs = current_docs()
for p in docs:
    check_doc(p, links_only=p.startswith(('.agents/', 'bench/')))
check_standards()
from unsafe_inventory import check as unsafe_check, summary as unsafe_summary
unsafe_problems, unsafe_counts = unsafe_check(os.getcwd())
problems.extend(unsafe_problems)
print(unsafe_summary(unsafe_counts))
# The documented-command contract: the command examples of these documents and
# the option tables of docs/configuration.md against the scripts' own parsers
# (cli_contract.py; DOC-10, HARNESS-02). Its coverage is limited and reported.
from cli_contract import check as cli_check, summary as cli_summary
cli_problems, cli_counts = cli_check(os.getcwd(), docs)
problems.extend(cli_problems)
print(cli_summary(cli_counts))
code = set()
for d in ['crates', 'scripts', 'tests', '.agents', 'bench']:
    for p in glob.glob(d + '/**/*', recursive=True):
        if os.path.isfile(p) and p.endswith(('.rs', '.py', '.sh', '.md', '.toml', '.h', '.flags')) and '/specs/tlc/' not in p:
            code.add(p)
for p in sorted(code):
    check_code(p)

from compat_check import check_files as compat_check
problems.extend(compat_check([*docs, *sorted(code)]))
from doc_tla import check_files as tla_check

example_counts = dict(probed=False, available=False, executed=0, failed=0, skipped=0)


def example_runner(command, **kwargs):
    probe = not example_counts['probed']
    example_counts['probed'] = True
    if not probe:
        example_counts['executed'] += 1
    try:
        result = subprocess.run(command, **kwargs)
    except (OSError, subprocess.TimeoutExpired):
        if not probe:
            example_counts['failed'] += 1
        raise
    if not probe and result.returncode:
        example_counts['failed'] += 1
    if probe:
        example_counts['available'] = result.returncode == 0
    return result


def example_note(message):
    print(message)
    skipped = re.search(r'parsing skipped \((\d+) blocks\)', message)
    if skipped:
        example_counts['skipped'] += int(skipped[1])
    if args.require_examples:
        problems.append(f'required example parsing unavailable: {message}')


problems.extend(tla_check([p for p in docs if p != 'AGENTS.md'], runner=example_runner, note=example_note))
if args.require_examples and not example_counts['available'] and not example_counts['skipped']:
    why = 'cannot parse a trivial module' if example_counts['probed'] else 'missing'
    problems.append(f'required example parsing unavailable: target/test-release/tlx {why}; '
                    'build with cargo build --profile test-release -p tlx')
executed, failed, skipped = (example_counts[k] for k in ('executed', 'failed', 'skipped'))
print(f'TLA+ parse-only: selected={executed + skipped} executed={executed} '
      f'passed={executed - failed} failed={failed} skipped={skipped}; model execution is not checked')

knobs = set(re.findall(r'"(TLX_[A-Z0-9_]+|CC)"', Path('crates/tlx-base/src/knobs.rs').read_text()))
abi = {'TLX_OK', 'TLX_ERR', 'TLX_STOP', 'TLX_MISS', 'TLX_UNSUPPORTED', 'TLX_ABI_VERSION'}
for p in docs:
    if p.startswith(('.agents/', 'bench/')):
        continue
    for ln, line in enumerate(Path(p).read_text(encoding='utf-8').splitlines(), 1):
        for m in re.finditer(r'\bTLX_[A-Z0-9_]*[A-Z0-9]\b', line):
            if m.group(0) not in knobs and m.group(0) not in abi:
                problems.append(f'{p}:{ln}: unknown variable {m.group(0)}')

STALE = (r'behavior_graph|BehaviorGraph|TLX_LIVE_REEXPLORE|NO_INIT_IN_CONSTRAINT|set_unreduced|DumpModel|LiveErrors|IrModel'
         r'|tree-walk|树遍历|Lowerer::new\b|check_graph|record_graph|live_edges|(?<![\w-])-ir\b|exec/eval\.rs'
         r'|Exec::for_region|TLX_IR_CLOSURES|tlx_fingerprint|TLX_MEMO\b|TLX_IR_INTERP|TLX_MIXED_LOOPS|TLX_MIXED_MEMO|TLX_NO_REGIONS')
for p in docs:
    if p.startswith(('.agents/', 'bench/')):
        continue
    for ln, line in enumerate(Path(p).read_text(encoding='utf-8').splitlines(), 1):
        for m in re.finditer(STALE, line):
            problems.append(f'{p}:{ln}: stale term {m.group(0)}')

for p in docs:
    for ln, line in enumerate(Path(p).read_text(encoding='utf-8').splitlines(), 1):
        for m in re.finditer(r'`((?:crates/)?tlx-[a-z]+/(?:src|tests|community|stdlib)/[A-Za-z0-9_./-]+?\.(?:rs|h|tla))', line):
            f = m.group(1)
            if not f.startswith('crates/'):
                f = 'crates/' + f
            if not os.path.exists(f):
                problems.append(f'{p}:{ln}: missing file {m.group(1)}')

from benchmarking.bench_records import check as performance_check; problems.extend(performance_check(os.getcwd(), sources=False))

for x in problems:
    print(x)
absent = [p for p in PUBLISHED_DOCS if not os.path.isfile(p)]
if absent:
    print(f'documents: absent from this checkout, not checked: {", ".join(absent)}')
print(f'-- {len(problems)} problems; {len(docs)} current docs, {len(code)} code/skill files scanned')
sys.exit(1 if problems else 0)
