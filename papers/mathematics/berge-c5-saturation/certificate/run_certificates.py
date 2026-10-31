#!/usr/bin/env python3
"""Decompress the three finite certificates, compile the verifier and check them all.

Usage: python3 certificate/run_certificates.py [--json OUT]

The verifier `verify_profiles.cpp` regenerates every incidence profile of a simple
three-uniform hypergraph with m hyperedges on min_n..max_n vertices (with at most the stated
number of isolated vertices) and consumes exactly one record per profile.  For the four- and
five-edge certificates it also checks that the listed isomorphism classes are canonical,
distinct, saturated and used.  It needs a C++17 compiler.
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

# (m, min_n, max_n, max_isolates, certificate, class list, expected records, expected classes)
RUNS = [
    (4, 0, 13, 1, "m4_all.cert.xz", "m4_classes.txt", 1332, 13),
    (5, 0, 16, 1, "m5_all.cert.xz", "m5_classes.txt", 56688, 32),
    (6, 11, 18, 0, "m6_n11plus.cert.xz", None, 311635, 0),
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", type=Path)
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
        for m, lo, hi, iso, cert, classes, expected, nclasses in RUNS:
            plain = work / cert.removesuffix(".xz")
            with lzma.open(DATA / cert) as src, plain.open("wb") as dst:
                shutil.copyfileobj(src, dst)
            command = [str(binary), str(m), str(lo), str(hi), str(iso), str(plain)]
            if classes:
                command.append(str(DATA / classes))
            start = time.monotonic()
            run = subprocess.run(command, capture_output=True, text=True)
            elapsed = time.monotonic() - start
            plain.unlink()
            if run.returncode != 0:
                raise SystemExit(f"{cert}: verifier failed: {run.stderr.strip()}")
            record = json.loads(run.stdout)
            if (not record.get("passed") or record.get("records") != expected
                    or record.get("classes") != nclasses):
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
