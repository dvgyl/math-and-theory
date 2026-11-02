# Fresh replay record

This directory records the fresh verification of this package run for its publication on 2 November 2026.

- [`build.log.xz`](build.log.xz): `lake build HarmonicBoundary HarmonicBoundary.AxiomAudit` in a fresh copy of [lean/](../lean/) with no build output, using Lean 4.35.0 (commit `eb6cafb7290e`) on Linux x86_64. Because no module imports Mathlib, this local replay used a copy of the lakefile without the Mathlib requirement; the CI workflow builds the unchanged project. All 55 project modules, the root module and the audit module compiled; the build took about three minutes. Absolute paths of the working copy are replaced by `<package>/lean`.
- [`axiom-inventory.json`](axiom-inventory.json): the summary output of `scripts/check_axiom_audit.py` on that log. All 15,771 declarations defined in the 53 project modules that define declarations, including generated and auxiliary ones, depend only on `propext`, `Classical.choice` and `Quot.sound`, and 497 depend on no axiom.
- [`checks.log`](checks.log): `python3 checks/run_checks.py --independent` with Python 3.13 and NetworkX 3.7. All seventeen package checkers and the six independent enumerations passed. The nauty-based census and closure were not rerun; the independent census and closures cover the same finite statements.

Compiled objects are not included. The CI workflow repeats the replay on every push.
