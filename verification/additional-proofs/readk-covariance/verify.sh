#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
mkdir -p verification
lake build 2>&1 | tee verification/build.log
lake env lean -j 1 Audit.lean 2>&1 | tee verification/axioms.txt
python3 scripts/check_audit.py verification/axioms.txt | tee verification/source-audit.txt
python3 scripts/finite_checks.py | tee verification/finite-checks.json
