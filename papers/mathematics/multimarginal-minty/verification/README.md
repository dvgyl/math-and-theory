# Fresh replay record

This directory records the fresh verification of this package run for its publication on 31 October 2026.

- [`build.log`](build.log): `lake build Minty Minty.AxiomAudit` in a fresh copy of `lean/` with no project build output, using Lean 4.19.0 (commit `6caaee842e94`) on Linux x86_64 and a clean checkout of Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b` whose modules were built from source on the same machine. All six project modules and the audit module were compiled.
- [`axiom-inventory.json`](axiom-inventory.json): the output of `scripts/check_axiom_audit.py` on that log. All 47 declarations defined in the project modules, 18 of them generated or auxiliary, depend only on `propext`, `Classical.choice` and `Quot.sound`.
- [`exact-check.json`](exact-check.json): the output of `certificate/verify_minty_exact.py`.

Machine-specific paths are replaced by `$REPLAY` (the replay working directory), `$LEAN_HOME` (the Lean distribution) and `$MATHLIB` (the Mathlib checkout). Compiled objects are not included. The CI workflow repeats the replay on every push.
