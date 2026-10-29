# Verification

All seven local Lean modules were freshly compiled with Lean 4.19.0 and mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The seven source compilations and the final axiom audit used explicit `--trust=0` and warnings as errors. All eleven audited theorem endpoints passed. Each uses only `propext`, `Classical.choice`, and `Quot.sound`. The source and object hashes, timestamps, return codes and axiom lists are in [receipt.json](verification/receipt.json).

The three Python standard-library arithmetic checkers also passed. The optional numerical search was not required. The README gives commands to reproduce both checks.

The formal result covers actual unique global projection or proximal minimizers and the entire infinite periodic trajectory. The finite-objective theorem also covers the unique constrained optimizer. Convexity, strong convexity, C2 regularity and Lipschitz-gradient properties of the smooth extension are proved in the manuscript and are outside the formal theorem. The receipt does not establish literature priority or external peer review.
