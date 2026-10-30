# Fresh replay record

This directory and the records inside [`../lean_p1_converse/`](../lean_p1_converse/) document the fresh Lean replay of this package run for its publication on 30 October 2026.

The run used Lean 4.35.0-rc3 (commit `470d5ce1400764999581fd26d5d72b00d990b0f4`) on Linux x86_64 and Mathlib `0db6cb99b412983de54b59ecc1b0b2747542cda3`, whose required modules (2,635 build jobs in total) were compiled from source on the same machine.

- After `lake clean mat_c_p1` removed the cancellation project's build output, `lean_p1_converse/verify.sh` removed its own, rebuilt all 58 modules of `MatCP1Converse` and the cancellation modules it imports, printed the exact statements of the main declarations and audited all 276 exported theorems. Its logs are in [`../lean_p1_converse/verification/`](../lean_p1_converse/verification/), and its summary with source hashes is [`../lean_p1_converse/VERIFICATION.json`](../lean_p1_converse/VERIFICATION.json).
- [`build-p1-root.log`](build-p1-root.log) records the build of the cancellation root module `MatCP1`, and [`lean_p1-axioms.log`](lean_p1-axioms.log) its audit: all ten audited cancellation endpoints depend only on `propext`, `Classical.choice` and `Quot.sound`.

Machine-specific paths are replaced by `$REPLAY` (the replay working directory) and `$LEAN_HOME` (the Lean distribution). Compiled objects are not included. The CI workflow repeats the replay on every push.
