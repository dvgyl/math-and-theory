# Lean formalizations

This directory contains the shared Lean formalizations for seven result families in Math and Theory. The other formal proofs use standalone pinned packages. The complete [manuscript map](../CONTENTS.md) links every paper to its proof environment and states its formal and conventional proof boundaries.

The shared library uses Lean 4.35.0 and the dependencies pinned in [lake-manifest.json](lake-manifest.json). Its 29 selected Comparator statements include equality, sharpness and positivity claims. The [formalization catalogue](formalization.yaml) links these statements to their manuscripts and configurations.

The `MathAndTheory` library contains the proofs. `Challenges` contains separate specifications with deliberate proof holes. `Solutions` proves their statement types. The proved library does not import `Challenges`.

Use the [verification guide](../verification/README.md) for build commands, transitive axiom audits, Comparator checks and independent kernels. It also links the standalone packages and their reproduction instructions. Only `propext`, `Classical.choice` and `Quot.sound` are accepted in proof dependencies. A source hash check is separate from a completed Lean build.

The Gyires [order-six](../verification/gyires-circulant-six/README.md), [permutation-polynomial](../verification/gyires-permutation-polynomial/README.md) and [rank-two](../verification/gyires-rank-two/README.md) packages supply further formal proofs for that family. Rank-two orders 2 through 8 are proved. General order-seven circulants and rank-two orders 9 through 15 remain incomplete in Lean; see [UNFINISHED.md](../UNFINISHED.md).

Lean verifies the stated propositions. It does not establish novelty, source identity or human peer review.
