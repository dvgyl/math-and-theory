#!/usr/bin/env python3
"""Replay the exact and numerical checks of this package in a temporary copy.

The checkers write their JSON reports next to themselves, so this program
copies checks/ to a temporary directory and runs each checker there with
`python3 -I`, adding only the checker's own directory to the import path.
NumPy, SciPy and SymPy are needed (requirements.txt); the Galois certificate
uses only the standard library.

    python3 checks/run_checks.py [--independent] [--keep DIR]
"""
import argparse
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

RUNNER = ("import runpy,sys,os;s=os.path.abspath(sys.argv[1]);"
          "sys.path.insert(0,os.path.dirname(s));sys.argv=sys.argv[1:];"
          "runpy.run_path(s,run_name='__main__')")

CORE = [
    ('Galois certificate (standard library, exact)', 'verify_galois_certificate.py'),
    ('companion polynomial and six-invariant rule (exact)', 'verify_companion_exact.py'),
    ('exact rational evaluator, 23 cases (exact)', 'verify_exact_rational.py'),
    ('primary Float64 checks, 800 one-sided instances', 'verify.py'),
    ('separate density-matrix implementation, 514 instances', 'independent_check.py'),
    ('success-probability lens and rate checks', 'extension_checks.py'),
    ('conditional-purity bound and cluster checks', 'conditional_checks.py'),
]
INDEPENDENT = [
    ('brute-force filter optimization against the closed formula', 'independent_bruteforce.py'),
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--independent', action='store_true',
                        help='also run the brute-force comparison written for this release')
    parser.add_argument('--keep', type=Path, help='keep the working copy and reports here')
    args = parser.parse_args()
    source = Path(__file__).resolve().parent
    work = Path(tempfile.mkdtemp(prefix='one-sided-f3-checks-'))
    tree = work / 'checks'
    shutil.copytree(source, tree, ignore=shutil.ignore_patterns('__pycache__', 'run_checks.py'))
    jobs = CORE + (INDEPENDENT if args.independent else [])
    failed = []
    for label, script in jobs:
        start = time.monotonic()
        result = subprocess.run([sys.executable, '-I', '-c', RUNNER, str(tree / script)],
                                cwd=tree, capture_output=True, text=True)
        status = 'PASS' if result.returncode == 0 else 'FAIL'
        print(f'{status}  {label}  [{script}, {time.monotonic() - start:.0f} s]', flush=True)
        if result.returncode:
            failed.append(script)
            print(result.stdout[-2000:], result.stderr[-2000:], sep='\n')
    if args.keep:
        shutil.copytree(tree, args.keep, dirs_exist_ok=True)
    shutil.rmtree(work)
    print(f'{len(jobs) - len(failed)} of {len(jobs)} checkers passed.')
    return 1 if failed else 0


if __name__ == '__main__':
    raise SystemExit(main())
