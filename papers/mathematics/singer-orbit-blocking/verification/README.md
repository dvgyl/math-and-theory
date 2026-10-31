# Fresh replay record

This directory records the fresh verification of this package run on 31 October 2026 with `python3 verify.py` in a fresh copy of the package on Linux x86_64, Lean 4.35.0 and Python 3. The dependency checkouts at the pinned revisions were copied from an earlier fetch; the script then fetched the official Mathlib cache and compiled every project module.

- [`build.log`](build.log): `lake build` of the 26 project modules against the official cache of Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. Lake compiled up to four modules at a time on a shared four-core machine; each of the sixteen certificate modules took between 251 and 447 seconds, and the build took 1376 seconds.
- [`axioms.log`](axioms.log): `lake env lean Audit.lean`. The module-wide audit covers 1090 declarations in 26 modules and rejects none; each of the 18 principal declarations depends only on `propext`, `Classical.choice` and `Quot.sound`.
- [`check_singer.json`](check_singer.json): output of `certificate/check_singer.py` on the witness, including the exhaustive search with 156,717 nodes.
- [`report.json`](report.json): summary written by `verify.py`.

Compiled objects are not included.
