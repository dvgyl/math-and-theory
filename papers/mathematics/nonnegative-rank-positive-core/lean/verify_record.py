#!/usr/bin/env python3
"""Validate fresh build, exact pins, upstream preservation, and all proof closures."""
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import sys

from generate_audit import declarations

ROOT = Path(__file__).resolve().parent
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
MATHLIB = '0db6cb99b412983de54b59ecc1b0b2747542cda3'
LEAN_COMMIT = '470d5ce1400764999581fd26d5d72b00d990b0f4'

def require(ok, message):
    if not ok:
        raise SystemExit(message)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def check_environment():
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    require((ROOT / 'lean-toolchain').read_text().strip() ==
            'leanprover/lean4:v4.35.0-rc3', 'Compiler version pin changed')
    for package in manifest['packages']:
        path = ROOT / '.lake/packages' / package['name']
        actual = subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD'], text=True).strip()
        require(actual == package['rev'], f"Dependency revision mismatch: {package['name']}")
        print(f"Dependency {package['name']}: {actual}")
    require(any(p['name'] == 'mathlib' and p['rev'] == MATHLIB
                for p in manifest['packages']), 'Mathlib pin changed')
    original = json.loads((ROOT / 'verification/upstream-sources.json').read_text())
    for path, digest in original['sha256'].items():
        require(sha(ROOT / path) == digest, f'Upstream source changed: {path}')
    print(f"Preserved upstream: {original['commit']}; {len(original['sha256'])} Lean source files")

def main():
    if sys.argv[1:] == ['--environment']:
        check_environment()
        return
    require(not sys.argv[1:], 'Use no arguments or --environment')
    sources = sorted((ROOT / 'MatCKronecker').glob('*.lean')) + sorted((ROOT / 'PositiveCore').glob('*.lean'))
    modules = {p.relative_to(ROOT).with_suffix('').as_posix().replace('/', '.'): p for p in sources}
    modules.update({name: ROOT / f'{name}.lean' for name in ('MatCKronecker', 'PositiveCore')})
    reached = set()
    def visit(name):
        if name in reached:
            return
        require(name in modules, f'Missing source for {name}')
        reached.add(name)
        for dep in re.findall(r'^(?:public )?import ((?:MatCKronecker|PositiveCore)(?:\.[\w]+)*)$',
                              modules[name].read_text(), re.M):
            visit(dep)
    visit('MatCKronecker')
    visit('PositiveCore')
    require(reached == set(modules), f'Unexported source modules: {set(modules)-reached}')
    decls = [d for p in sources for d in declarations(p)]
    names = sorted(n for _, n in decls)
    require(len(names) == len(set(names)), 'Duplicate declaration names')
    requested = re.findall(r'^#print axioms (\S+)$', (ROOT / 'AxiomAudit.lean').read_text(), re.M)
    require(sorted(requested) == names, 'The audit must name every authored declaration')
    env = (ROOT / 'verification/environment.log').read_text()
    build = (ROOT / 'verification/build.log').read_text()
    audit = (ROOT / 'verification/axioms.log').read_text()
    require('version 4.35.0-rc3,' in env and f'commit {LEAN_COMMIT},' in env, 'Compiler pin mismatch')
    require(f'Dependency mathlib: {MATHLIB}' in env, 'Mathlib revision not checked')
    require('Build completed successfully' in build, 'Missing successful aggregate build')
    require(not re.search(r'\berror:', build + audit), 'Final verification logs contain an error')
    require('⋯' not in audit, 'A printed theorem type was elided')
    built = set(re.findall(r'\bBuilt ((?:MatCKronecker|PositiveCore)(?:\.[\w]+)*)(?=\s|$)', build))
    require(built == set(modules), f'Fresh authored-module coverage mismatch: {set(modules)-built}')
    axioms = {}
    for name, raw in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", audit):
        require(name not in axioms, f'Duplicate proof-closure output: {name}')
        deps = [s.strip() for s in raw.split(',') if s.strip()]
        require(set(deps) <= ALLOWED, f'Nonstandard dependency in {name}: {deps}')
        axioms[name] = deps
    for name in re.findall(r"'([^']+)' does not depend on any axioms", audit):
        require(name not in axioms, f'Duplicate proof-closure output: {name}')
        axioms[name] = []
    require(sorted(axioms) == names, f'Missing proof-closure output: {set(names)-set(axioms)}')
    for path in modules.values():
        require(not re.search(r'\b(sorry|admit|axiom|native_decide)\b', path.read_text()),
                f'Forbidden proof construct in {path.relative_to(ROOT)}')
    require('sorryAx' not in audit and 'Lean.ofReduceBool' not in audit, 'Untrusted proof closure')
    check_environment()
    paths = set(modules.values()) | {ROOT / 'AxiomAudit.lean'}
    paths |= set(ROOT.glob('*.py')) | set(ROOT.glob('*.sh'))
    paths |= {ROOT / p for p in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']}
    paths |= {ROOT / 'verification' / p for p in ['environment.log', 'build.log', 'axioms.log',
                                                'upstream-sources.json', 'lean_app_path_compat.c']}
    record = {
        'recorded_utc': datetime.now(timezone.utc).isoformat(),
        'fresh_project_build': True,
        'build_exit_code': 0,
        'axiom_audit_exit_code': 0,
        'lean_version': '4.35.0-rc3',
        'lean_commit': LEAN_COMMIT,
        'mathlib_commit': MATHLIB,
        'executable_path_compatibility_shim_used': any(
            Path(p).name == 'lean_app_path_compat.so'
            for p in os.environ.get('LD_PRELOAD', '').split(':') if p),
        'freshly_built_modules': sorted(built),
        'audited_declarations': len(axioms),
        'audited_theorems': sum(k in ('theorem', 'lemma') for k, _ in decls),
        'allowed_foundational_axioms': sorted(ALLOWED),
        'axioms': dict(sorted(axioms.items())),
        'source_and_log_sha256': {str(p.relative_to(ROOT)): sha(p) for p in sorted(paths)},
        'verification_boundary': ('All authored source modules were rebuilt after deleting their build directory. '
          'Pinned Mathlib dependency caches were retained. Proofs use only Lean standard foundations. '
          'The optional Linux executable-path compatibility shim changes no parser, elaborator, evaluator, or kernel. '
          'External Python certificate checks are additional arithmetic checks and are not premises of Lean theorems. '
          'This verification does not establish novelty or journal readiness.')
    }
    (ROOT / 'VERIFICATION.json').write_text(json.dumps(record, indent=2) + '\n')
    print(f"Verified {len(built)} freshly built modules and {len(axioms)} complete proof closures.")

if __name__ == '__main__':
    main()
