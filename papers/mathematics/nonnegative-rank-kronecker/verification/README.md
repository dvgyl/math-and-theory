# Fresh replay record

This directory and the records inside [`../lean/`](../lean/) document the fresh verification of this package run for its publication on 30 October 2026.

- The Lean replay used Lean 4.35.0-rc3 (commit `470d5ce1400764999581fd26d5d72b00d990b0f4`) on Linux x86_64 with the dependency checkouts pinned in `lean/lake-manifest.json`; the Mathlib objects at revision `0db6cb99b412983de54b59ecc1b0b2747542cda3` came from the official Mathlib cache. In a fresh copy of the project, `lean/verify.sh` removed the project's build output, rebuilt all 14 modules with Lake's local artifact cache disabled and audited all 130 declarations defined in them; every one depends only on `propext`, `Classical.choice` and `Quot.sound`. Its logs are in [`../lean/verification/`](../lean/verification/) and its summary with source hashes is [`../lean/VERIFICATION.json`](../lean/VERIFICATION.json).
- [`certificate-check.json`](certificate-check.json) is the output of `certificate/exact_certificate.py --verify-only`; regenerating the certificate from the construction reproduced `C11_NMF109.json` byte for byte.
- [`independent-check.json`](independent-check.json) is the output of `certificate/check_factorization.py`.

Machine-specific paths are replaced by `$PACKAGE` (the package directory). Compiled objects are not included. The CI workflow repeats the Lean replay and both certificate checks on every push.
