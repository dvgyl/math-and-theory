# Fresh replay record

This directory records the fresh verification of this package run for its publication on 31 October 2026, with `python3 verify.py` in a fresh copy of the package on Linux x86_64, Lean 4.35.0 and Python 3.13.

- [`build.log`](build.log): `lake build` of the project modules against the official cache of Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`; all project modules were compiled.
- [`axioms.log`](axioms.log): `lake env lean Audit.lean`. Every audited declaration depends only on `propext`, `Classical.choice` and `Quot.sound`.
- [`check_spectrum.json`](check_spectrum.json): output of `certificate/check_spectrum.py` on the four witnesses.
- [`report.json`](report.json): summary written by `verify.py`, including the certificate-checker results.

Compiled objects are not included.
