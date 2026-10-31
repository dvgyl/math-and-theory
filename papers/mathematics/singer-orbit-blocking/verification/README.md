# Replay record

This directory records the checks of this package run on 31 October 2026 on Linux x86_64 with Lean 4.35.0 and Python 3.

- [`build.log`](build.log): the development build of the project in a working copy, with Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` from the official cache. The sixteen certificate modules were compiled three at a time; each took between 217 and 337 seconds of wall-clock time on a shared machine, and the whole build took 1888 seconds. The log keeps the certificate modules and the end of the final build.
- [`axioms.log`](axioms.log): `lake env lean Audit.lean`. The module-wide audit covers 1090 declarations in 26 modules and rejects none; each of the 18 principal declarations depends only on `propext`, `Classical.choice` and `Quot.sound`.
- [`check_singer.json`](check_singer.json): output of `certificate/check_singer.py` on the witness, including the exhaustive search with 156,717 nodes.

Compiled objects are not included.
