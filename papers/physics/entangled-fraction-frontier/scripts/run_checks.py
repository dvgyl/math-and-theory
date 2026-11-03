#!/usr/bin/env python3
"""Replay the exact and numerical checks of the package from a temporary copy.

Usage: python3 scripts/run_checks.py [--skip-sdp] [--no-independent] [--log-dir DIR]

The script copies analysis/ and scripts/independent_check.py to a temporary
directory and runs each checker there with `python3 -I`, so that nothing is
imported from the working directory. The 18 checkers in analysis/ write their
result files next to themselves inside the copy; the recorded files in the
package are not modified. A checker passes when it exits with status 0, which
each one does only after its own assertions succeed. --skip-sdp omits the two
checkers that call a semidefinite-programming solver (check_sdp_reduction.py
and check_negativity.py); that run is deliberately incomplete. The independent
checker (scripts/independent_check.py) was written for this release and is run
last. Requires the packages in analysis/requirements.txt. Exact rational and
symbolic checks are certificates; floating-point and solver checks detect
errors and are not proofs.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
CHECKERS = [
    'verify_results.py', 'symbolic_checks.py', 'geometry_checks.py',
    'highdim_canonical_checks.py', 'exact_expanded_certificates.py',
    'check_expanded_results.py', 'verify_purity_envelope.py',
    'core_uniqueness_checks.py', 'all_optimizer_rank_checks.py',
    'low_rank_optimizer_checks.py', 'capacity_checks.py', 'saturation_checks.py',
    'dual_stability_checks.py', 'saturation_inertia_checks.py', 'check_sdp_reduction.py',
    'check_negativity.py', 'tensor_entanglement_checks.py', 'collective_capacity_checks.py',
]
SDP = {'check_sdp_reduction.py', 'check_negativity.py'}


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument('--skip-sdp', action='store_true')
    parser.add_argument('--no-independent', action='store_true')
    parser.add_argument('--log-dir', type=Path)
    args = parser.parse_args()
    env = dict(os.environ, OPENBLAS_NUM_THREADS='1', OMP_NUM_THREADS='1',
               MKL_NUM_THREADS='1', MPLBACKEND='Agg', PYTHONHASHSEED='0')
    records = []
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp)
        shutil.copytree(ROOT / 'analysis', work / 'analysis')
        shutil.copy2(ROOT / 'scripts/independent_check.py', work / 'independent_check.py')
        jobs = [(work / 'analysis' / name, []) for name in CHECKERS
                if not (args.skip_sdp and name in SDP)]
        if not args.no_independent:
            jobs.append((work / 'independent_check.py',
                         ['--output', str(work / 'independent_check.json')]))
        for script, extra in jobs:
            begin = time.monotonic()
            proc = subprocess.run([sys.executable, '-I', str(script), *extra], cwd=work,
                                  env=env, text=True, capture_output=True)
            output = proc.stdout + proc.stderr
            record = {'script': script.relative_to(work).as_posix(),
                      'sha256': hashlib.sha256(script.read_bytes()).hexdigest(),
                      'exit_code': proc.returncode,
                      'seconds': round(time.monotonic() - begin, 1)}
            records.append(record)
            print(json.dumps(record), flush=True)
            if args.log_dir:
                args.log_dir.mkdir(parents=True, exist_ok=True)
                (args.log_dir / (script.stem + '.log')).write_text(output)
            if proc.returncode:
                print(output, file=sys.stderr)
                break
        if not args.no_independent and args.log_dir and (work / 'independent_check.json').exists():
            shutil.copy2(work / 'independent_check.json', args.log_dir / 'independent_check.json')
    ok = len(records) == len(jobs) and all(r['exit_code'] == 0 for r in records)
    print(('All %d checks passed.' % len(records)) if ok else 'A check failed.', flush=True)
    return 0 if ok else 1


if __name__ == '__main__':
    raise SystemExit(main())
