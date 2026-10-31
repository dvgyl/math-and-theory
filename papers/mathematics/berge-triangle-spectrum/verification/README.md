# Fresh replay record

This directory records the fresh verification of this package run on 31 October 2026 for the extended Lean project, with `python3 verify.py` in a fresh copy of the package on Linux x86_64, Lean 4.35.0 and Python 3.13. The dependency checkouts at the pinned revisions were copied from an earlier fetch; the script then fetched the official Mathlib cache and compiled every project module.

- [`build.log`](build.log): `lake build` of the project modules against the official cache of Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`; the project modules compiled in about 26 seconds in total, and the whole run took 38 seconds.
- [`axioms.log`](axioms.log): `lake env lean Audit.lean`. Each of the 33 audited declarations depends only on `propext`, `Classical.choice` and `Quot.sound`, or on a subset of them.
- [`check_spectrum.json`](check_spectrum.json): output of `certificate/check_spectrum.py` on the four witnesses.
- [`report.json`](report.json): summary written by `verify.py`, including the certificate-checker results.

Compiled objects are not included.
