# Fresh replay record

This directory records the fresh verification of this package run for its publication on 1 November 2026.

- [`build.log`](build.log), [`axioms.txt`](axioms.txt) and [`certificate.json`](certificate.json): the package verifier [`lean/verify.py`](../lean/verify.py) with `--trust 0`, run in a fresh copy of the package using Lean 4.19.0 (commit `6caaee842e94`) on Linux x86_64 and the official Mathlib cache for revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. All 89 modules (62 earlier, 9 inherited, 15 stability, 1 attainment, 2 bridge) were compiled from source into a fresh output directory, about 13.5 minutes of compilation. All 144 audited declarations depend only on `propext`, `Classical.choice` and `Quot.sound`. The certificate binds the source and verifier hashes.
- [`upload-chain-replay.json`](upload-chain-replay.json): a summary of the fresh replay of the upload's own chained verifiers at `--trust=0`: the earlier 62-module project, all 49 modules of the unpublished preceding extension (190 audits), the 15 stability modules (67 audits), the bridge (15 audits) and the attainment module (2 audits), each passing with only the same three axioms. It took about 23 minutes. The chained verifiers and the 40 preceding modules not imported here are not included.

The interval certificates were rerun from a copy of [`certificates/`](../certificates/) with python-flint 0.9.0 at 128 and 192 bits; all 27,972 leaves passed at both precisions, and the 128-bit reports are stored there. The two exact rational checks also passed.

Machine-specific paths are replaced by `$REPLAY` (the report directory), `$LEAN_HOME` (the Lean distribution), `$MATHLIB` and `$ELAN_HOME`. Compiled objects are not included. The CI workflow repeats the verifier with the default import trust level and the 128-bit certificate checks on every push.
