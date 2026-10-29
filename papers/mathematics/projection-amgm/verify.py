#!/usr/bin/env python3
"""Rebuild the two matrix proofs and audit named endpoints and dependencies."""
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
FINITE = 'ProjectionCounterexample.three_projection_counterexample'
FAMILY = 'ProjectionFamily.no_finite_loewner_constant'
AUDIT = {FINITE, FAMILY, 'ProjectionCounterexample.exact_quadratic_form',
         'ProjectionFamily.exact_quadratic_form'}


def check_axioms(output, expected):
    reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", output)
    names = [name for name, _ in reports]
    if len(names) != len(expected) or set(names) != set(expected):
        raise RuntimeError(f'Incomplete or duplicate named axiom audit: {names}')
    for name, body in reports:
        found = {x.strip() for x in body.split(',') if x.strip()}
        if not found <= ALLOWED:
            raise RuntimeError(f'Unapproved axioms for {name}: {sorted(found - ALLOWED)}')
    if re.search(r'\b(sorryAx|Lean\.ofReduceBool)\b', output):
        raise RuntimeError('Unapproved proof dependency')


def self_test():
    def report(names):
        return '\n'.join(f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]"
                         for name in names)
    check_axioms(report(sorted(AUDIT)), AUDIT)
    invalid = [report([FINITE] * 4), report(sorted(AUDIT - {FAMILY}) + ['Wrong.target']),
               report(sorted(AUDIT - {FAMILY})), report(sorted(AUDIT)).replace('propext', 'sorryAx', 1)]
    for output in invalid:
        try:
            check_axioms(output, AUDIT)
        except RuntimeError:
            continue
        raise RuntimeError('Axiom-audit negative control did not fail')
    print('PASS: named endpoint audit and four negative controls')


def limits():
    resource.setrlimit(resource.RLIMIT_AS, (8 * 1024 ** 3, 8 * 1024 ** 3))


def run(args, expected=None):
    result = subprocess.run(args, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, timeout=900, preexec_fn=limits)
    print(result.stdout, end='', flush=True)
    if result.returncode:
        raise SystemExit(result.returncode)
    if expected is not None:
        check_axioms(result.stdout, expected)
    return result.stdout


def without_comments(source):
    out, i, depth = [], 0, 0
    while i < len(source):
        if source.startswith('/-', i):
            depth += 1
            i += 2
        elif depth and source.startswith('-/', i):
            depth -= 1
            i += 2
        elif depth:
            if source[i] == '\n': out.append('\n')
            i += 1
        elif source[i] == '"':
            out.append(' ')
            i += 1
            while i < len(source):
                if source[i] == '\\':
                    i += 2
                elif source[i] == '"':
                    i += 1
                    break
                else:
                    if source[i] == '\n': out.append('\n')
                    i += 1
        elif source.startswith('--', i):
            end = source.find('\n', i)
            i = len(source) if end < 0 else end
        else:
            out.append(source[i]); i += 1
    if depth: raise ValueError('Unclosed block comment')
    return ''.join(out)


def dependency_fingerprints(prefix):
    packages = ROOT / '.lake/packages'
    roots = [(p, p / '.lake/build/lib/lean') for p in sorted(packages.iterdir()) if p.is_dir()]
    roots.append((prefix / 'src/lean', prefix / 'lib/lean'))
    queue, records = [], {}
    for source in (ROOT / 'ProjectionAMGM').glob('*.lean'):
        queue.extend(re.findall(r'^import\s+(\S+)', without_comments(source.read_text()), re.M))
    while queue:
        name = queue.pop()
        if name in records:
            continue
        rel = Path(*name.split('.'))
        matches = [(s / rel.with_suffix('.lean'), o / rel.with_suffix('.olean'))
                   for s, o in roots if (s / rel.with_suffix('.lean')).is_file()]
        if len(matches) != 1:
            raise RuntimeError(f'Unresolved or ambiguous dependency: {name}')
        source, obj = matches[0]
        if not obj.is_file():
            raise RuntimeError(f'Missing dependency object: {name}')
        records[name] = {'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
                         'object_sha256': hashlib.sha256(obj.read_bytes()).hexdigest()}
        clean = without_comments(source.read_text())
        if name != 'Init' and not re.search(r'^prelude\s*$', clean, re.M):
            queue.append('Init')
        for line in re.findall(r'^import\s+([^\n]+)', clean, re.M):
            queue.extend(line.split())
    return records


def check_environment():
    version = run(['lake', 'env', 'lean', '--version']).strip()
    if not re.search(r'\bversion 4\.19\.0\b', version):
        raise RuntimeError('Lean 4.19.0 is required')
    prefix = Path(run(['lake', 'env', 'lean', '--print-prefix']).strip())
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    packages = manifest['packages']
    if len(packages) != 9:
        raise RuntimeError('Expected the nine pinned dependencies')
    for package in packages:
        path = ROOT / '.lake/packages' / package['name']
        actual = run(['git', '-C', str(path), 'rev-parse', 'HEAD']).strip()
        if actual != package['rev']:
            raise RuntimeError(f'Dependency pin mismatch: {package["name"]}')
        if run(['git', '-C', str(path), 'status', '--porcelain', '--untracked-files=no']).strip():
            raise RuntimeError(f'Tracked dependency changes: {package["name"]}')
    return prefix


def main():
    os.chdir(ROOT)
    self_test()
    if sys.argv[1:] == ['--self-test']:
        return
    if sys.argv[1:]:
        raise SystemExit('Usage: python3 verify.py [--self-test]')
    prefix = check_environment()
    before = dependency_fingerprints(prefix)
    outputs = ROOT / '.lake/build/lib/lean/ProjectionAMGM'
    outputs.mkdir(parents=True, exist_ok=True)
    for name, endpoint in [('Counterexample', FINITE), ('Family', FAMILY)]:
        target = outputs / (name + '.olean')
        target.unlink(missing_ok=True)
        run(['lake', 'env', 'lean', '--trust=0', '-DwarningAsError=true', '-j1',
             '-o', str(target), 'ProjectionAMGM/' + name + '.lean'], {endpoint})
    run(['lake', 'env', 'lean', '--trust=0', '-DwarningAsError=true', '-j1', 'Audit.lean'], AUDIT)
    if dependency_fingerprints(prefix) != before:
        raise RuntimeError('Dependency source or object changed during verification')
    run([sys.executable, '-O', 'verify_exact.py'])
    print('PASS: two matrix proofs, named endpoint types and axioms, unchanged dependencies, exact arithmetic')


if __name__ == '__main__':
    main()
