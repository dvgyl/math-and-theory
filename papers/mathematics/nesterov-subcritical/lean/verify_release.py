#!/usr/bin/env python3
"""Strict from-source verification of the planar damping-r Nesterov escape tree.

Every module of this tree is copied into a fresh directory and compiled from
source, one at a time, with `lean --trust=0 -j1 -DwarningAsError=true` into a
fresh object directory.  Only the pinned Mathlib build and its pinned
dependencies are put on LEAN_PATH next to that fresh object directory; no
object file of this tree is reused.  The script also

  * checks the Lean release (4.19.0, commit 6caaee842e94), `lean-toolchain`,
    and that Mathlib and every dependency are checked out at the revisions
    pinned in `lake-manifest.json` without tracked modifications;
  * checks that the lakefile roots, the module list below and the `.lean`
    files present are the same set, and that every import is either Mathlib or
    an earlier module of the list;
  * scans the sources (comments and strings removed) for prohibited tokens and
    allows only the options `autoImplicit`, `maxHeartbeats` and `linter.*`;
  * runs `Audit.lean` and requires every `#print axioms` result in every log to
    be a subset of {propext, Classical.choice, Quot.sound}, the headline
    theorems to depend on exactly these three, and all audit lines present;
  * writes a JSON receipt (status PASS only if everything above succeeds).

Standard library only.  Usage:

  python3 -I verify_release.py --lean-home /tmp/leanenv/lean-4.19.0-linux \
      --mathlib /tmp/leanenv/mathlib4 --out verification/run-NAME
"""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import os
import re
import shutil
import subprocess
import time

# Topological order (each module imports only Mathlib or earlier entries).
MODULES = [
    # P (damping-two release): the global convex C^1 planar Huber valley, unchanged.
    'RadialHuber', 'ValleyModel',
    # H (continuous-time Hilbert threshold release), all modules unchanged.
    'ConvexProjection', 'PowerAlgebra', 'PowerModel', 'PowerNormal', 'PowerEstimates',
    'PowerExterior', 'ScalarModelBounds', 'PowerValley', 'PowerMinimizers', 'ExponentSelection',
    'FiniteEuler', 'ValleyPath', 'FiniteExcursion', 'MoreauTrajectory', 'FiniteActual',
    'GeneralVolterraKernel', 'GeneralVolterraOperator', 'GeneralVolterraCalculus',
    'HilbertSum', 'BlockScaling', 'TimeScaling', 'HilbertModel', 'HilbertEscape', 'HighDamping',
    'SharpThreshold', 'LowDampingPotential', 'LowDampingTrajectory', 'LowDampingMain',
    'LowDampingHilbert', 'AllPositiveThreshold',
    # D (discrete-time threshold release): its 16 new modules, unchanged.
    'NAGBasic', 'NAGConjugacy', 'NAGHilbertModel', 'NAGVelocity', 'NAGHilbertEscape',
    'NAGStability', 'UniformTaylor', 'NAGODELimit', 'VolterraAcceleration',
    'NAGPlanarExcursion', 'NAGDescent', 'NAGHighDamping', 'NAGAxisLift', 'NAGLowDamping',
    'NAGLowHilbert', 'NAGSharpThreshold',
    # New: planar escape for every damping 0 < r <= 2.
    'PlanarEnergy', 'EulerObstruction', 'PlanarInvariants', 'PlanarUnbounded',
    'PlanarTrajectory', 'PlanarMain', 'PlanarAllDamping',
]
AUDIT = 'Audit'
HEADLINES = [
    # H
    'NesterovSharpThreshold.exists_subcritical_norm_divergent_flow',
    'NesterovSharpThreshold.sharp_boundedness_threshold',
    'NesterovSharpThreshold.exists_positive_subcritical_norm_divergent_flow',
    'NesterovSharpThreshold.sharp_boundedness_threshold_all_positive',
    'NesterovHighDamping.bounded_distance',
    # D
    'DiscreteNesterov.sharp_discrete_boundedness_threshold',
    'DiscreteNesterov.exists_subcritical_discrete_norm_divergence',
    'DiscreteNesterov.exists_discrete_norm_divergence_below_three',
    # planar
    'NesterovPlanar.planar_valley_escape',
    'NesterovPlanar.every_planar_trajectory_escapes',
    'NesterovPlanar.planar_escape_all_low_damping',
]
EXPECTED_AUDIT_AXIOM_LINES = 50
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
EXPECTED_TOOLCHAIN = 'leanprover/lean4:v4.19.0'
EXPECTED_MATHLIB_REV = 'c44e0c8ee63ca166450922a373c7409c5d26b00b'
EXPECTED_LEAN_VERSION = ('version 4.19.0', 'commit 6caaee842e94')
PROHIBITED_WORDS = re.compile(
    r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by|extern|opaque|'
    r'elab|elab_rules|macro|macro_rules|syntax|run_cmd|run_elab|run_meta|'
    r'initialize|builtin_initialize)\b')
PROHIBITED_COMMANDS = re.compile(r'#(eval|exit|reduce)\b')
ALLOWED_OPTIONS = {'autoImplicit', 'maxHeartbeats'}
ALLOWED_OPTION_PREFIXES = ('linter.',)
CONFIG_FILES = ['verify_release.py', 'lake-manifest.json', 'lean-toolchain', 'lakefile.lean']
ACTIVE_RECEIPT_PATH = None


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def command(args, cwd=None):
    return subprocess.check_output(args, cwd=cwd, text=True).strip()


def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def strip_comments_and_strings(text):
    out = []
    i = 0
    depth = 0
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1
                i += 2
            elif text.startswith('-/', i):
                depth -= 1
                i += 2
            else:
                i += 1
        elif text.startswith('/-', i):
            depth = 1
            i += 2
        elif text.startswith('--', i):
            j = text.find('\n', i)
            i = len(text) if j < 0 else j
        elif text[i] == '"':
            i += 1
            while i < len(text) and text[i] != '"':
                i += 2 if text[i] == '\\' else 1
            i += 1
            out.append(' ')
        else:
            out.append(text[i])
            i += 1
    if depth:
        raise RuntimeError('Unclosed Lean block comment')
    return ''.join(out)


def dependency_dir(mathlib, name):
    """A dependency nested in a standalone Mathlib checkout, or its sibling in a Lake project."""
    nested = mathlib / '.lake/packages' / name
    return nested if nested.is_dir() else mathlib.parent / name


def write_receipt(path, data):
    path.write_text(json.dumps(data, indent=2, ensure_ascii=False) + '\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--lean-home', required=True, type=Path,
                        help='Lean 4.19.0 distribution (contains bin/lean)')
    parser.add_argument('--mathlib', required=True, type=Path,
                        help='Mathlib checkout with built .lake/build/lib/lean')
    parser.add_argument('--out', required=True, type=Path,
                        help='New or empty verification directory')
    args = parser.parse_args()
    try:
        verify(args)
    except BaseException as exc:
        if ACTIVE_RECEIPT_PATH is not None and ACTIVE_RECEIPT_PATH.exists():
            data = json.loads(ACTIVE_RECEIPT_PATH.read_text())
            data['status'] = 'FAILED'
            data['failure'] = type(exc).__name__ + ': ' + str(exc)
            data['finished_utc'] = now()
            write_receipt(ACTIVE_RECEIPT_PATH, data)
        raise


def check_tree(src):
    """Static checks of the source tree; returns per-module source hashes."""
    toolchain = (src / 'lean-toolchain').read_text().strip()
    if toolchain != EXPECTED_TOOLCHAIN:
        raise RuntimeError('Unexpected lean-toolchain: ' + toolchain)
    names = MODULES + [AUDIT]
    if len(set(names)) != len(names):
        raise RuntimeError('Duplicate module in MODULES')
    present = {p.stem for p in src.glob('*.lean') if p.name != 'lakefile.lean'}
    if present != set(names):
        raise RuntimeError(f'Module list mismatch: missing {sorted(set(names) - present)}, '
                           f'unlisted {sorted(present - set(names))}')
    lakefile_raw = (src / 'lakefile.lean').read_text()
    lakefile = strip_comments_and_strings(lakefile_raw)
    roots = re.search(r'roots\s*:=\s*#\[([^\]]*)\]', lakefile)
    if not roots:
        raise RuntimeError('No roots in lakefile.lean')
    root_names = re.findall(r'`([A-Za-z_][A-Za-z0-9_.]*)', roots.group(1))
    if set(root_names) != set(names) or len(root_names) != len(names):
        raise RuntimeError(f'lakefile roots differ from the module list: {root_names}')
    if not re.search(r'@\s*"' + EXPECTED_MATHLIB_REV + '"', lakefile_raw):
        raise RuntimeError('lakefile does not pin the expected Mathlib revision')
    hashes = {}
    imports = {}
    for idx, name in enumerate(names):
        path = src / (name + '.lean')
        raw = path.read_text()
        code = strip_comments_and_strings(raw)
        bad = PROHIBITED_WORDS.search(code)
        if bad:
            raise RuntimeError(f'Prohibited source token in {name}: {bad.group()}')
        bad = PROHIBITED_COMMANDS.search(code)
        if bad:
            raise RuntimeError(f'Prohibited command in {name}: {bad.group()}')
        for opt in re.findall(r'\bset_option\s+([A-Za-z_][A-Za-z0-9_.]*)', code):
            if opt not in ALLOWED_OPTIONS and not opt.startswith(ALLOWED_OPTION_PREFIXES):
                raise RuntimeError(f'Option not on the allow-list in {name}: {opt}')
        if re.search(r'\boptions\b|\bpp\.|\bdebug\.|\btrust\b', code):
            raise RuntimeError(f'Suspicious option-like token in {name}')
        mods = re.findall(r'^\s*import\s+([A-Za-z0-9_.]+)', code, flags=re.M)
        for m in mods:
            if m.startswith('Mathlib.'):
                continue
            if m not in names[:idx]:
                raise RuntimeError(f'{name} imports {m}, which is neither Mathlib nor earlier in MODULES')
        imports[name] = mods
        hashes[path.name] = sha(path)
    return hashes, imports


def verify(args):
    global ACTIVE_RECEIPT_PATH
    started = time.monotonic()
    src = Path(__file__).resolve().parent
    out = args.out.resolve()
    dist = args.lean_home.resolve()
    mathlib = args.mathlib.resolve()
    if out.exists() and any(out.iterdir()):
        raise RuntimeError('Output directory must be empty; use a new path')
    out.mkdir(parents=True, exist_ok=True)
    receipt_path = out / 'receipt.json'
    ACTIVE_RECEIPT_PATH = receipt_path
    config_hashes = {name: sha(src / name) for name in CONFIG_FILES}
    write_receipt(receipt_path, {'status': 'VALIDATING', 'config_sha256': config_hashes,
                                 'started_utc': now()})
    frozen = out / 'sources'
    objects = out / 'objects'
    logs = out / 'logs'
    for d in (frozen, objects, logs):
        d.mkdir()

    # Pinned dependencies.
    manifest = json.loads((src / 'lake-manifest.json').read_text())
    pins = {}
    for p in manifest['packages']:
        directory = mathlib if p['name'] == 'mathlib' else dependency_dir(mathlib, p['name'])
        actual = command(['git', '-C', str(directory), 'rev-parse', 'HEAD'])
        if actual != p['rev']:
            raise RuntimeError(f"Revision mismatch for {p['name']}: {actual} != {p['rev']}")
        dirty = command(['git', '--no-optional-locks', '-C', str(directory), 'status',
                         '--porcelain', '--untracked-files=no'])
        if dirty:
            raise RuntimeError(f"Tracked modifications in {p['name']}")
        pins[p['name']] = {'revision': actual, 'url': p['url']}
    if pins.get('mathlib', {}).get('revision') != EXPECTED_MATHLIB_REV:
        raise RuntimeError('Mathlib is not at the expected revision')

    # Lean release.
    lean = dist / 'bin/lean'
    version = command([str(lean), '--version'])
    if not all(token in version for token in EXPECTED_LEAN_VERSION):
        raise RuntimeError('Unexpected Lean release: ' + version)

    # Static source checks.
    hashes, imports = check_tree(src)
    for name in MODULES + [AUDIT]:
        shutil.copy2(src / (name + '.lean'), frozen / (name + '.lean'))

    paths = [objects, mathlib / '.lake/build/lib/lean']
    paths += [dependency_dir(mathlib, p['name']) / '.lake/build/lib/lean'
              for p in manifest['packages'] if p['name'] != 'mathlib']
    env = os.environ.copy()
    env['LEAN_PATH'] = os.pathsep.join(map(str, paths))
    env['LEAN_SYSROOT'] = str(dist)
    receipt = {
        'started_utc': now(),
        'lean_version': version,
        'lean_binary': str(lean),
        'lean_binary_sha256': sha(lean),
        'lean_toolchain': EXPECTED_TOOLCHAIN,
        'pinned_dependencies': pins,
        'source_sha256': hashes,
        'imports': imports,
        'config_sha256': config_hashes,
        'lean_path': env['LEAN_PATH'],
        'lean_sysroot': env['LEAN_SYSROOT'],
        'allowed_axioms': sorted(STANDARD),
        'verification_policy': ('Fresh copy of every source compiled in order into a fresh '
                                'object directory with --trust=0 -j1 -DwarningAsError=true; '
                                'only pinned Mathlib/dependency builds on LEAN_PATH; '
                                'all #print axioms results must be standard'),
        'modules': [],
        'status': 'RUNNING',
    }
    write_receipt(receipt_path, receipt)

    all_axiom_reports = {}
    for name in MODULES + [AUDIT]:
        cmd = [str(lean), '--trust=0', '-j1', '-DwarningAsError=true',
               '-o', str(objects / (name + '.olean')),
               '-i', str(objects / (name + '.ilean')), name + '.lean']
        start = time.monotonic()
        print(f'Checking {name} (trust=0)', flush=True)
        log = logs / (name + '.log')
        with log.open('w') as stream:
            result = subprocess.run(cmd, cwd=frozen, env=env, stdout=stream,
                                    stderr=subprocess.STDOUT)
        elapsed = round(time.monotonic() - start, 3)
        content = log.read_text()
        record = {'module': name, 'trust': 0, 'returncode': result.returncode,
                  'command': cmd, 'cwd': str(frozen), 'elapsed_seconds': elapsed,
                  'log_sha256': sha(log),
                  'olean_sha256': sha(objects / (name + '.olean'))
                  if (objects / (name + '.olean')).exists() else None}
        receipt['modules'].append(record)
        write_receipt(receipt_path, receipt)
        if result.returncode:
            print(content, flush=True)
            raise RuntimeError(f'Compilation of {name} failed (exit {result.returncode})')
        if re.search(r"declaration uses 'sorry'|\berror\b|\bwarning\b", content):
            print(content, flush=True)
            raise RuntimeError(f'Error/warning/sorry text in the log of {name}')
        reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", content, flags=re.S)
        none = re.findall(r"'([^']+)' does not depend on any axioms", content)
        module_reports = {}
        for decl, entry in reports:
            axioms = {a.strip() for a in entry.split(',') if a.strip()}
            if not axioms <= STANDARD:
                raise RuntimeError(f'Unapproved axioms in {name} for {decl}: {sorted(axioms)}')
            module_reports[decl] = sorted(axioms)
        for decl in none:
            module_reports[decl] = []
        if len(re.findall(r'depends on axioms', content)) != len(reports):
            raise RuntimeError(f'Unparsed axiom report in {name}')
        record['axiom_reports'] = module_reports
        all_axiom_reports.update(module_reports)
        if name == AUDIT:
            if len(reports) + len(none) != EXPECTED_AUDIT_AXIOM_LINES:
                raise RuntimeError(f'Audit: found {len(reports) + len(none)} axiom reports, '
                                   f'expected {EXPECTED_AUDIT_AXIOM_LINES}')
            for decl in HEADLINES:
                if set(module_reports.get(decl, ['<missing>'])) != STANDARD:
                    raise RuntimeError(f'Audit: {decl} axioms {module_reports.get(decl)}')
                # The printed signature may start with universe parameters, e.g. `.{u_1} {E : Type u_1}`.
                if not re.search(r'^' + re.escape(decl) + r'(\.\{[^}]*\})?\s+[{(\[]', content, flags=re.M):
                    raise RuntimeError(f'Audit: no #check statement for {decl}')
            receipt['audit_log'] = content
            receipt['headline_axioms'] = {d: module_reports[d] for d in HEADLINES}
        write_receipt(receipt_path, receipt)

    for name, expected in hashes.items():
        if sha(src / name) != expected or sha(frozen / name) != expected:
            raise RuntimeError('Source changed during verification: ' + name)
    for name, expected in config_hashes.items():
        if sha(src / name) != expected:
            raise RuntimeError('Verification configuration changed: ' + name)
    receipt['all_axiom_reports'] = all_axiom_reports
    receipt['all_audited_axioms_standard'] = True
    receipt['total_elapsed_seconds'] = round(time.monotonic() - started, 3)
    receipt['status'] = 'PASS'
    receipt['finished_utc'] = now()
    write_receipt(receipt_path, receipt)
    print('PASS: fresh trust-zero source build of every module and standard-axiom audit.',
          flush=True)


if __name__ == '__main__':
    main()
