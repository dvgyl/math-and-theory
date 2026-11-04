# Verification scope

The fresh [GitHub proof replay](https://github.com/dvgyl/math-and-theory/actions/runs/41884387516) rebuilt all 30 authored modules and audited 267 declarations, including 206 theorems and lemmas. The exact dependency lock, source hashes and logs are preserved in `lean/VERIFICATION.json` and `lean/verification/`. Every reported axiom dependency is in `propext`, `Classical.choice`, or `Quot.sound`.

The exact-arithmetic replay checked three activation certificates, byte-identical regeneration, all 16 cone-generator pairs, and the earlier width-109 certificate with two checkers. Negative-factor mutation checks failed with nonzero exit codes under Python optimization.

The general lower bound and original mixed-block equality have formal proofs. The uniform neighbourhood formulas and the all-size saturation endpoint retain conventional proofs. The new seed lower bound relies on cited classical work. Formal checking does not establish historical priority or external peer review. See `FORMAL_CORRESPONDENCE.md` for statement-level coverage.
