#!/usr/bin/env python3
"""Check explicit NYLL source rules without compiling or changing caches.

Copyright (c) 2026 Naganori Yamaguchi. Apache-2.0.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729

The default checks all maintained sources. --base compares with a Git revision
and reports newly introduced occurrences; existing debt is not declared fixed.
Semantic instance ownership and mathematical assumptions still need review.
"""
from __future__ import annotations

# Keep historical flat module imports and CLI entry points compatible.
import sys as _tool_sys
from pathlib import Path as _ToolPath
_tool_sys.path.insert(0, str(_ToolPath(__file__).resolve().parents[1]))

import argparse
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
import re
import subprocess

from cache_sources import strip_comments_strings

ROOT = Path(__file__).resolve().parents[2]
RULES = {
    'unbounded-simplification': r'(?<![\w.\[])simp(?![\w\'?])',
    'search-tactic': r'(?<![\w.])(?:aesop|solve_by_elim|exact\?|apply\?|simp\?|simpa\?)(?![\w\'])',
    'source-option': r'(?m)^\s*set_option\b',
    'unproved-term': r'(?<![\w.])(?:sorry|admit)(?![\w\'])',
    'diagnostic-command': r'(?m)^\s*#(?:check|print|eval|reduce|synth)\b',
    'environment-internals': r'\b(?:scopedEnvExtensionsRef|mkPrivateName|activeScopes|stateStack|addAlias)\b',
    # The pinned Lean Core deprecates these in favor of ite_eq_* / dite_eq_*.
    'deprecated-conditional-lemma': r'(?<![\w.])(?:if_pos|if_neg|dif_pos|dif_neg)(?![\w\'])',
}


@dataclass(frozen=True)
class Finding:
    rule: str
    line: int
    context: str


def findings(source: str) -> list[Finding]:
    clean = strip_comments_strings(source)
    # Attribute arguments such as @[reassoc (attr := simp)] are not tactics.
    # Mask only attribute brackets, preserving line locations and nested lists.
    masked = list(clean)
    for attribute in re.finditer(r'@\s*\[|\battribute\s+\[', clean):
        start = clean.index('[', attribute.start())
        depth = 0
        for offset in range(start, len(clean)):
            if clean[offset] == '[':
                depth += 1
            elif clean[offset] == ']':
                depth -= 1
            if clean[offset] != '\n':
                masked[offset] = ' '
            if depth == 0:
                break
    clean = ''.join(masked)
    lines = clean.splitlines()
    result = []
    for rule, pattern in RULES.items():
        for match in re.finditer(pattern, clean):
            if rule == 'unbounded-simplification':
                following = clean[match.end():].lstrip()
                if re.match(r'only\b', following) or following.startswith((']', ',')):
                    continue
            # Leading command whitespace may include preceding empty lines.
            offset = match.start() + len(match.group()) - len(match.group().lstrip())
            line = clean.count('\n', 0, offset) + 1
            context = ' '.join(lines[line - 1].split())
            result.append(Finding(rule, line, context))
    return sorted(result, key=lambda f: (f.line, f.rule))


def new_findings(source: str, previous: str) -> list[Finding]:
    remaining = Counter((f.rule, f.context) for f in findings(previous))
    result = []
    for finding in findings(source):
        key = finding.rule, finding.context
        if remaining[key]:
            remaining[key] -= 1
        else:
            result.append(finding)
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', help='Report new violations relative to this Git revision')
    args = parser.parse_args()
    if args.base:
        base = subprocess.check_output(
            ['git', 'rev-parse', '--verify', args.base + '^{commit}'], cwd=ROOT, text=True
        ).strip()
    else:
        base = None
    old_paths = set()
    if base:
        old_paths = set(subprocess.check_output(
            ['git', 'ls-tree', '-r', '--name-only', base, '--', 'Nyll', 'Nyll.lean'],
            cwd=ROOT, text=True).splitlines())
        changed = subprocess.check_output(
            ['git', 'diff', '--name-only', base, '--', 'Nyll', 'Nyll.lean'],
            cwd=ROOT, text=True).splitlines()
        added = subprocess.check_output(
            ['git', 'ls-files', '--others', '--exclude-standard', '--', 'Nyll', 'Nyll.lean'],
            cwd=ROOT, text=True).splitlines()
        paths = [ROOT / p for p in sorted(set(changed + added))
                 if p.endswith('.lean') and (ROOT / p).is_file()]
    else:
        paths = sorted((ROOT / 'Nyll').rglob('*.lean')) + [ROOT / 'Nyll.lean']
    counts: Counter[str] = Counter()
    for path in paths:
        relative = path.relative_to(ROOT).as_posix()
        source = path.read_text(encoding='utf-8')
        if base and relative in old_paths:
            old = subprocess.run(['git', 'show', base + ':' + relative], cwd=ROOT,
                                 capture_output=True, check=False)
            if old.returncode:
                raise RuntimeError(old.stderr.decode(errors='replace'))
            current = new_findings(source, old.stdout.decode('utf-8'))
        else:
            current = findings(source)
        for finding in current:
            counts[finding.rule] += 1
            print(f'{relative}:{finding.line}: {finding.rule}: {finding.context}')
    scope = 'new occurrences' if base else 'all occurrences'
    print(f'{scope}: {sum(counts.values())}; files checked: {len(paths)}; {dict(counts)}')
    return int(bool(counts))


if __name__ == '__main__':
    raise SystemExit(main())
