"""Replay every exact and numerical check of the package and compare with the recorded outputs.

Usage: python3 scripts/run_checks.py [--quick]

The script copies calculations/ to a temporary directory, runs each checker
there with `python -I` (so that nothing is imported from the working
directory; a checker's own folder is put on the module path only for the
checkers that import a sibling module), and compares each JSON output with
the recorded file in the package. Environment fields are ignored;
floating-point values are compared with a relative tolerance of 1e-6 and an
absolute tolerance of 1e-9. The two figure scripts are run and must exit
cleanly. Requires the packages in calculations/requirements.txt. --quick
skips the three slowest checkers (the two direct-optimizer audits and
release_check.py), which together take about eight minutes.
"""
from pathlib import Path
import argparse
import json
import math
import os
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
IGNORED = {"environment", "python", "numpy", "scipy", "sympy", "matplotlib", "platform"}

CHECKS = [
    ("calculations/exact_examples.py", [], "calculations/exact_results.json", False),
    ("calculations/check_extensions.py", [], "calculations/extension_implementation_results.json", True),
    ("calculations/audit_spectral_cases.py", [], "calculations/independent_spectral_audit.json", False),
    ("calculations/independent_audit/check_spectral.py", [],
     "calculations/independent_audit/check_results.json", False),
    ("calculations/independent_audit/check_spectral.py", ["--additional"],
     "calculations/independent_audit/additional_results.json", False),
    ("calculations/extensions/independent_checks.py", [], "calculations/extensions/independent_results.json", False),
    ("calculations/extensions/additional_exact_checks.py", [],
     "calculations/extensions/additional_exact_results.json", True),
    ("calculations/extensions/rank2_checks.py", [], "calculations/extensions/rank2_scan.json", True),
    ("calculations/extensions/nonunique_optimizer_example.py", [],
     "calculations/extensions/nonunique_optimizer_example.json", False),
    ("calculations/extensions/bilateral_family_certificate.py", [],
     "calculations/extensions/bilateral_family_certificate.json", False),
    ("calculations/original_input/original_state_whitening_checks.py", [],
     "calculations/original_input/original_state_whitening_results.json", False),
    ("calculations/original_input/check_original_success.py", [],
     "calculations/original_input/original_success_results.json", True),
    ("calculations/check_filter_reduction.py", [], "calculations/filter_reduction_numeric.json", False),
    ("calculations/release_check.py", ["--output", "{out}"], "calculations/release_check.json", False),
]
SLOW = {("calculations/independent_audit/check_spectral.py", ()),
        ("calculations/independent_audit/check_spectral.py", ("--additional",)),
        ("calculations/release_check.py", ("--output", "{out}"))}
FIGURES = ["calculations/make_figures.py", "calculations/make_original_success_figures.py"]


def strip(value):
    if isinstance(value, dict):
        return {k: strip(v) for k, v in value.items() if k not in IGNORED}
    if isinstance(value, list):
        return [strip(v) for v in value]
    return value


def compare(a, b, path="$"):
    if isinstance(a, dict) and isinstance(b, dict):
        if set(a) != set(b):
            return f"{path}: keys differ"
        for k in a:
            err = compare(a[k], b[k], f"{path}.{k}")
            if err:
                return err
        return None
    if isinstance(a, list) and isinstance(b, list):
        if len(a) != len(b):
            return f"{path}: lengths differ"
        for i, (x, y) in enumerate(zip(a, b)):
            err = compare(x, y, f"{path}[{i}]")
            if err:
                return err
        return None
    if isinstance(a, bool) or isinstance(b, bool) or not isinstance(a, (int, float)) \
            or not isinstance(b, (int, float)):
        return None if a == b else f"{path}: {a!r} != {b!r}"
    return None if math.isclose(a, b, rel_tol=1e-6, abs_tol=1e-9) else f"{path}: {a} != {b}"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--quick", action="store_true")
    args = parser.parse_args()
    failures = []
    # The uploaded runner fixed these for reproducible floating-point results.
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1", OPENBLAS_NUM_THREADS="1",
               OMP_NUM_THREADS="1", PYTHONHASHSEED="0", MPLBACKEND="Agg")
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp) / "package"
        shutil.copytree(ROOT / "calculations", work / "calculations")
        for script, arguments, recorded, sibling in CHECKS:
            if args.quick and (script, tuple(arguments)) in SLOW:
                print(f"skipped  {script} {' '.join(arguments)}".rstrip())
                continue
            path = work / script
            out = work / recorded
            shown = f"{script} {' '.join(arguments)}".rstrip()
            arguments = [a.replace("{out}", str(out)) for a in arguments]
            if sibling:
                boot = ("import runpy, sys; sys.path.insert(0, sys.argv[1]); sys.argv = sys.argv[2:]; "
                        "runpy.run_path(sys.argv[0], run_name='__main__')")
                command = [sys.executable, "-I", "-c", boot, str(path.parent), str(path), *arguments]
            else:
                command = [sys.executable, "-I", str(path), *arguments]
            run = subprocess.run(command, cwd=tmp, env=env, capture_output=True, text=True)
            if run.returncode != 0:
                failures.append(script)
                print(f"FAILED   {shown}\n{run.stderr[-2000:]}")
                continue
            expected = strip(json.loads((ROOT / recorded).read_text()))
            observed = strip(json.loads(out.read_text()))
            err = compare(expected, observed)
            if err:
                failures.append(script)
                print(f"DIFFERS  {shown}: {err}")
            else:
                print(f"ok       {shown}")
        for script in FIGURES:
            boot = ("import runpy, sys; sys.path.insert(0, sys.argv[1]); sys.argv = sys.argv[2:]; "
                    "runpy.run_path(sys.argv[0], run_name='__main__')")
            path = work / script
            plot = subprocess.run([sys.executable, "-I", "-c", boot, str(path.parent), str(path)],
                                  cwd=tmp, env=env, capture_output=True, text=True)
            print(f"ok       {script}" if plot.returncode == 0 else f"FAILED   {script}\n{plot.stderr[-2000:]}")
            if plot.returncode != 0:
                failures.append(script)
    if failures:
        raise SystemExit(f"{len(failures)} check(s) failed: {failures}")
    print("All checks reproduced the recorded outputs.")


if __name__ == "__main__":
    main()
