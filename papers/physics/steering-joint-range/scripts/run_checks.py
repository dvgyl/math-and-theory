"""Replay every exact and numerical check of the package and compare with the recorded outputs.

Usage: python3 scripts/run_checks.py [--quick]

The script copies calculations/ to a temporary directory, runs each checker
there with `python -I` (so that nothing is imported from the working
directory; a checker's own folder is put on the module path only for the two
checkers that import a sibling module), and compares each JSON output with
the recorded file in the package. Environment fields (interpreter and
library versions) are ignored; floating-point values are compared with a
relative tolerance of 1e-6 and an absolute tolerance of 1e-9, so roundoff
residuals may differ between platforms. Requires the packages in
calculations/requirements.txt. --quick skips the 20,000-state rerun of
reproduce.py.
"""
from pathlib import Path
import argparse
import json
import math
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
IGNORED = {"environment", "python", "numpy", "scipy", "sympy", "matplotlib", "platform"}

# (script, arguments, output written by the script, recorded output, needs sibling import)
CHECKS = [
    ("calculations/reproduce_v2.py", [], "calculations/results_v2.json", False),
    ("calculations/reproduce.py", ["--samples", "20000"], "calculations/results.json", False),
    ("calculations/one_sided_filter.py", [], "calculations/one_sided_results.json", True),
    ("calculations/exact_filter_certificate.py", [], "calculations/exact_filter_certificates.json", False),
    ("calculations/exact_orbit_certificate.py", [], "calculations/exact_orbit_certificates.json", False),
    ("calculations/exact_physical_example.py", [], "calculations/exact_physical_example.json", False),
    ("calculations/verify_probability_geometry.py", [], "calculations/probability_geometry_checks.json", False),
    ("calculations/independent/independent_audit.py", ["--samples", "4096"],
     "calculations/independent/independent_audit.json", False),
    ("calculations/independent/verify_geometry.py", ["--output", "{out}"],
     "calculations/independent/geometry_checks.json", False),
    ("calculations/independent/verify_one_sided.py", ["--output", "{out}"],
     "calculations/independent/one_sided_checks.json", True),
    ("calculations/independent/exact_new_results.py", ["--output", "{out}"],
     "calculations/independent/exact_new_results.json", False),
]


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
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp) / "package"
        shutil.copytree(ROOT / "calculations", work / "calculations")
        (work / "figures").mkdir()
        for script, arguments, recorded, sibling in CHECKS:
            if args.quick and script.endswith("/reproduce.py"):
                print(f"skipped  {script}")
                continue
            path = work / script
            out = work / recorded
            arguments = [a.replace("{out}", str(out)) for a in arguments]
            if sibling:
                boot = ("import runpy, sys; sys.path.insert(0, sys.argv[1]); sys.argv = sys.argv[2:]; "
                        "runpy.run_path(sys.argv[0], run_name='__main__')")
                command = [sys.executable, "-I", "-c", boot, str(path.parent), str(path), *arguments]
            else:
                command = [sys.executable, "-I", str(path), *arguments]
            run = subprocess.run(command, cwd=tmp, capture_output=True, text=True)
            if run.returncode != 0:
                failures.append(script)
                print(f"FAILED   {script}\n{run.stderr[-2000:]}")
                continue
            expected = strip(json.loads((ROOT / recorded).read_text()))
            observed = strip(json.loads(out.read_text()))
            err = compare(expected, observed)
            if err:
                failures.append(script)
                print(f"DIFFERS  {script}: {err}")
            else:
                print(f"ok       {script}")
        plot = subprocess.run([sys.executable, "-I", str(work / "calculations/plot_v2.py"),
                               "--output", str(work / "figures")], cwd=tmp, capture_output=True, text=True)
        print("ok       calculations/plot_v2.py" if plot.returncode == 0 else "FAILED   calculations/plot_v2.py")
        if plot.returncode != 0:
            failures.append("calculations/plot_v2.py")
    if failures:
        raise SystemExit(f"{len(failures)} check(s) failed: {failures}")
    print("All checks reproduced the recorded outputs.")


if __name__ == "__main__":
    main()
