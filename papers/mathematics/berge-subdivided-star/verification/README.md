# Fresh replay record

This directory records the fresh verification of this package run for its publication on 1 November 2026.

- [`build.log`](build.log): `lake build BergeBroom BergeBroom.AxiomAudit`, run by `scripts/verify.sh` in a fresh copy of the package with no project build output, using Lean 4.35.0 (commit `eb6cafb7290e`) on Linux x86_64 and the official Mathlib cache for revision `56a005855ea17e0b0958f73ec801ae140b0a1679`. All fourteen project modules, the root module and the audit module were compiled with warnings treated as errors; the script took about one minute.
- [`axiom-inventory.json`](axiom-inventory.json): the output of `scripts/check_axiom_audit.py` on that log. All 570 declarations defined in the project modules, including generated and auxiliary ones, depend only on `propext`, `Classical.choice` and `Quot.sound`.

Compiled objects are not included. The CI workflow repeats the replay on every push.
