#!/usr/bin/env python3
"""Reproduce exact arithmetic, source preservation, and optionally the clean Lean build.

Without --lean this checks the recorded Lean source/log hashes, not a new kernel
run. With --lean it first invokes lean/verify.sh, which deletes local project
build outputs and rebuilds all authored modules. Dependencies must be installed
as explained in VERIFY.md. Everything else uses Python's standard library.
"""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run_json(args, cwd=ROOT):
    result = subprocess.run(args, cwd=cwd, check=True, capture_output=True, text=True)
    return json.loads(result.stdout)


def verify(fresh_lean=False):
    if fresh_lean:
        subprocess.run(["bash", "verify.sh"], cwd=ROOT / "lean", check=True)
    provenance = json.loads((ROOT / "upstream/PROVENANCE.json").read_text())
    snapshot = ROOT / provenance["snapshot"]
    for name, expected in provenance["sha256"].items():
        require(digest(snapshot/name) == expected, f"Upstream snapshot changed: {name}")

    certs = [ROOT/f"certificates/activation_s{s}.json" for s in (2, 3, 5)]
    activation = run_json([sys.executable, "-O", "computations/check_certificate.py",
                           *map(str, certs)])
    require(all(x["status"] == "PASS" for x in activation), "Activation check failed")
    with tempfile.TemporaryDirectory(prefix="positive-core-certificates-") as temporary:
        generated = run_json([sys.executable, "-O", "computations/generate.py",
                              "--s", "2", "3", "5", "--write", temporary])
        for cert in certs:
            require(cert.read_bytes() == (Path(temporary)/cert.name).read_bytes(),
                    f"Regeneration is not byte-identical: {cert.name}")
    cone = run_json([sys.executable, "-O", "computations/cone_certificate.py",
                     "--check", "certificates/cone_obstruction.json"])
    original_a = run_json([sys.executable, "certificate/exact_certificate.py",
                          "--verify-only", "certificate/C11_NMF109.json"], snapshot)
    original_b = run_json([sys.executable, "certificate/check_factorization.py"], snapshot)
    require(original_a["status"] == original_b["status"] == "PASS", "Original replay failed")

    record_path = ROOT/"lean/VERIFICATION.json"
    require(record_path.is_file(), "Missing Lean record; install dependencies and use --lean")
    record = json.loads(record_path.read_text())
    for name, expected in record["source_and_log_sha256"].items():
        require(digest(ROOT/"lean"/name) == expected, f"Lean record no longer matches: {name}")
    require(record["fresh_project_build"] is True and record["build_exit_code"] == 0 and
            record["axiom_audit_exit_code"] == 0, "Invalid recorded Lean result")
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    require(all(set(ax) <= allowed for ax in record["axioms"].values()),
            "Nonstandard recorded axiom dependency")
    require(len(record["axioms"]) == record["audited_declarations"], "Audit count mismatch")
    return {"status": "PASS", "upstream_files_preserved": len(provenance["sha256"]),
            "activation_certificates": activation, "regeneration": generated,
            "regenerated_certificates_byte_identical": True,
            "cone_pairings_checked": cone["generator_pair_count"],
            "original_exact_replay": original_a, "original_independent_replay": original_b,
            "fresh_lean_build_this_invocation": fresh_lean,
            "stored_lean_source_and_log_hashes_valid": True,
            "recorded_lean_module_count": len(record["freshly_built_modules"]),
            "recorded_lean_declarations": record["audited_declarations"],
            "recorded_lean_theorems": record["audited_theorems"],
            "boundary": "External integer/rational checks do not certify literature priority. "
                        "Without --lean, the stored Lean record is validated but not rerun."}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", action="store_true", help="Run the clean Lean build and audit first")
    parser.add_argument("--output", type=Path, help="Also save the complete JSON report")
    args = parser.parse_args()
    result = json.dumps(verify(args.lean), indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(result)
    print(result, end="")
