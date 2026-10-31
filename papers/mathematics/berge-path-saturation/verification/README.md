# Fresh replay record

This directory records the fresh verification of this package run for its publication on 31 October 2026.

- [`build.log`](build.log): `lake build BergePath BergePath.AxiomAudit` in a fresh copy of `lean/` with no project build output, using Lean 4.35.0 (commit `eb6cafb7290e`) on Linux x86_64 and the official Mathlib cache for revision `56a005855ea17e0b0958f73ec801ae140b0a1679`. All three project modules, the root module and the audit module were compiled; the project build took about 30 seconds.
- [`axiom-inventory.json`](axiom-inventory.json): the output of `scripts/check_axiom_audit.py` on that log. All 191 declarations defined in the project modules, including generated and auxiliary ones, depend only on `propext`, `Classical.choice` and `Quot.sound`.
- [`witness-check.json`](witness-check.json): the output of `certificate/check_witness.py --json`, an exhaustive search over all Berge paths and all absent triples for `(m, n) = (10, 34)`, `(10, 50)` and `(11, 56)`.

Compiled objects are not included. The CI workflow repeats the replay on every push.
