#!/usr/bin/env python3
"""Decompress the six finite certificates, compile the verifier and check them all.

Usage: python3 certificate/run_certificates.py [--json OUT] [--skip-m7]

The verifier `verify_profiles.cpp` regenerates every incidence profile of a simple
three-uniform hypergraph with m hyperedges and no isolated vertex on min_n..max_n vertices
and consumes exactly one exclusion record per profile.  It needs a C++17 compiler.
"""
import argparse
import json
import lzma
import shutil
import subprocess
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
DATA = HERE / "data"

# (m, min_n, max_n, certificate, class list, expected record count)
RUNS = [
    (3, 6, 9, "m3_n6plus.cert.xz", None, 21),
    (4, 8, 12, "m4_n8plus.cert.xz", None, 261),
    (5, 10, 15, "m5_n10plus.cert.xz", None, 4664),
    (6, 12, 18, "m6_n12plus.cert.xz", None, 107740),
    (6, 11, 11, "n11_m6_classification.cert.xz", "n11_m6_classes.txt", 203895),
    (7, 13, 21, "m7_n13plus.cert.xz", None, 10592111),
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", type=Path)
    parser.add_argument("--skip-m7", action="store_true",
                        help="omit the 10,592,111-record seven-edge certificate")
    args = parser.parse_args()
    compiler = shutil.which("g++") or shutil.which("c++")
    if compiler is None:
        raise SystemExit("A C++17 compiler (g++) is required")
    results = []
    with tempfile.TemporaryDirectory() as work:
        work = Path(work)
        binary = work / "verify_profiles"
        subprocess.run([compiler, "-O3", "-std=c++17", str(HERE / "verify_profiles.cpp"),
                        "-o", str(binary)], check=True)
        for m, lo, hi, cert, classes, expected in RUNS:
            if args.skip_m7 and m == 7:
                continue
            plain = work / cert.removesuffix(".xz")
            with lzma.open(DATA / cert) as src, plain.open("wb") as dst:
                shutil.copyfileobj(src, dst)
            command = [str(binary), str(m), str(lo), str(hi), "0", str(plain)]
            if classes:
                command.append(str(DATA / classes))
            start = time.monotonic()
            run = subprocess.run(command, capture_output=True, text=True)
            elapsed = time.monotonic() - start
            plain.unlink()
            if run.returncode != 0:
                raise SystemExit(f"{cert}: verifier failed: {run.stderr.strip()}")
            record = json.loads(run.stdout)
            if not record.get("passed") or record.get("records") != expected:
                raise SystemExit(f"{cert}: unexpected verifier output {record}")
            record["certificate"] = cert
            record["seconds"] = round(elapsed, 2)
            results.append(record)
            print(json.dumps(record))
    summary = {"verified": True, "runs": results}
    if args.json:
        args.json.write_text(json.dumps(summary, indent=2) + "\n")


if __name__ == "__main__":
    main()
