# Fresh replay record

This directory records the verification of this package run for its publication on 31 October 2026.

- [`build.log`](build.log): `lake build BergeC4 BergeC4.AxiomAudit` in a copy of `lean/` with no project build output, using Lean 4.35.0 on Linux x86_64 and a prebuilt Mathlib at revision `56a005855ea17e0b0958f73ec801ae140b0a1679`. All four project modules, the root module and the audit module were compiled; the project build took about 30 seconds.
- [`axiom-inventory.json`](axiom-inventory.json): the output of `scripts/check_axiom_audit.py` on that log. All 263 declarations defined in the project modules, including generated and auxiliary ones, depend only on `propext`, `Classical.choice` and `Quot.sound`.
- [`construction-check.json`](construction-check.json): the output of `certificate/check_construction.py --max-n 40 --json`, an exhaustive standard-library check of the upper construction for `9 ≤ n ≤ 40`, of the witnesses for `3 ≤ n ≤ 8` and of sample values of the lower bound.
- [`certificate-check.json`](certificate-check.json): the output of `certificate/run_certificates.py`, the independent C++ verifier (compiled with g++ 13 and `-O3 -std=c++17`) run on all six certificates, with record counts and timings.

Compiled objects and decompressed certificates are not included. The CI workflow repeats the Lean build, the audit, the construction check and the five smaller certificates on every push.
