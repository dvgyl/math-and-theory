# Fresh replay record

This directory records the fresh verification of this package, run for its publication on 3 November 2026.

- [`build.log.xz`](build.log.xz): `lake build MilneResearch ProjectAxiomAudit` in a fresh copy of [lean/](../lean/) with no project build output, using Lean 4.32.0 (commit `8c9756b28d64`) on Linux x86_64 and the pinned Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997` from its official build cache, with the committed lakefile and manifest. All six modules and the audit module compiled from source in about five minutes. The 29 warnings are style linters in `AllProofs.lean`.
- [`axiom-inventory.json`](axiom-inventory.json): the output of `scripts/check_axiom_audit.py` on that log. The audit covers all 620 declarations defined in the six modules (494 theorems), including all 421 declarations named in the sources; all 620 depend only on `propext`, `Classical.choice` and `Quot.sound`. No code-generation auxiliaries occur under Lean 4.32.
- [`checks.log`](checks.log): `python3 -I scripts/run_checks.py` with Python 3.13, NumPy 2.3.5, SciPy 1.17.0, SymPy 1.14.0, CVXPY 1.6.5 and Clarabel 0.11.1. All 18 package checkers and the independent checker passed; [`independent-check.json`](independent-check.json) is the independent checker's report (39 checks).

The upload's own replay compiled the extension modules against a precompiled base object and documented a Lake configuration that does not build; this record replaces it with a full build from source. Compiled objects are not included. The CI workflow repeats the Lean build and the audit on every push.
