"""Replay the exact SymPy checks in a temporary copy and compare with the frozen records.

Usage: python3 scripts/run_exact_checks.py
Run it with an interpreter that has the packages in verification/requirements.txt.
The four exact scripts write their reports next to themselves; this runner copies
verification/ to a temporary directory, runs each script there, requires every
reported check to pass, and requires each regenerated report to equal the
committed one byte for byte. The committed files are never modified.
"""
from pathlib import Path
import json
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = {
    "class_d_verify.py": "class_d_verify_output.json",
    "new_results_verify.py": "new_results_verify_output.json",
    "exact_sdp_certificates.py": "exact_sdp_certificates.json",
    "verify_mirror_formulas.py": None,
}


def main():
    summary = {}
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp) / "verification"
        shutil.copytree(ROOT / "verification", work)
        for script, report in SCRIPTS.items():
            run = subprocess.run([sys.executable, "-I", str(work / script)], cwd=tmp,
                                 capture_output=True, text=True, check=False)
            if run.returncode != 0:
                raise SystemExit(f"{script} failed:\n{run.stdout}\n{run.stderr}")
            if report is None:
                # This script prints PASS lines; its record is the frozen stdout.
                frozen = (ROOT / "verification" / "mirror_formulas_output.txt").read_text()
                if run.stdout != frozen or "FAIL" in run.stdout:
                    raise SystemExit(f"{script}: output differs from the frozen record")
                summary[script] = {"passed": run.stdout.count("PASS"), "failed": 0}
                continue
            fresh = (work / report).read_bytes()
            if fresh != (ROOT / "verification" / report).read_bytes():
                raise SystemExit(f"{script}: regenerated {report} differs from the committed file")
            data = json.loads(fresh)
            if data.get("failed") != 0:
                raise SystemExit(f"{script}: reported failures {data.get('failed')}")
            if "passed" in data:
                summary[script] = {"passed": data["passed"], "failed": 0}
            else:
                summary[script] = {"optimization_certificates": data["optimization_certificates"],
                                   "containment_certificates": data["containment_certificates"],
                                   "failed": 0}
    print(json.dumps({"verified": True, "scripts": summary}, indent=2))


if __name__ == "__main__":
    main()
