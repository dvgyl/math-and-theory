# Fresh replay record

This directory records the verification of this package run for its publication on 31 October 2026.

- [`build.log`](build.log): `lake build BergeC5 BergeC5.AxiomAudit` in a copy of `lean/` with no project build output, using Lean 4.35.0 on Linux x86_64 and a prebuilt Mathlib at revision `56a005855ea17e0b0958f73ec801ae140b0a1679`. All four project modules, the root module and the audit module were compiled; the project build took about 30 seconds.
- [`axiom-inventory.json`](axiom-inventory.json): the output of `scripts/check_axiom_audit.py` on that log. All 344 declarations defined in the project modules, including generated and auxiliary ones, depend only on `propext`, `Classical.choice` and `Quot.sound`.
- [`construction-check.json`](construction-check.json): the output of `certificate/check_construction.py --max-n 60 --json`, an exhaustive standard-library check of every claimed pair `(n, m)` for `7 ≤ n ≤ 60`, of the cone sizes for `5 ≤ n ≤ 36`, of the expansion families and of the small witnesses; it reports no failure.
- [`certificate-check.json`](certificate-check.json): the output of `certificate/run_certificates.py`, the independent C++ verifier (compiled with g++ 13 and `-O3 -std=c++17`) run on all three certificates, with record and class counts and timings.

Compiled objects and decompressed certificates are not included.
