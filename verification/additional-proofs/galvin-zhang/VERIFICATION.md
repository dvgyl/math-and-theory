# Formal statements and verification

The proof uses Lean 4.19.0 and Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. All 18 project source files compiled from source in a new build directory. The eight printed axiom reports cover four declarations in `Main.lean` and again in `Audit.lean`. They use only `propext`, `Classical.choice`, and `Quot.sound`.

## Main theorem

`DominationULC.galvin_zhang_conjecture` proves ultra-log-concavity for powers of both paths and cycles. It quantifies over every natural n and ℓ.

`DominationULC.galvin_zhang_normalized` states the real-valued normalized inequality. For 1 ≤ k < n, it gives

    (dₖ₋₁ / binom(n,k−1)) (dₖ₊₁ / binom(n,k+1)) ≤ (dₖ / binom(n,k))².

`DominationULC.path_domination_weighted` and `DominationULC.cycle_domination_weighted` state the equivalent integer inequalities

    (k+1)(n−k+1)dₖ₋₁dₖ₊₁ ≤ k(n−k)dₖ².

The binomial denominators are positive on this range. The positive domination counts have no internal zero because domination is preserved when a vertex is added to a set.

## Definitions and correspondence

`Dominates G s` requires each vertex to be in s or adjacent to a member of s. `dominationCount G k` counts the k-element subsets with this property.

`pathPower n ℓ` uses ordinary distance on the labels `Fin n`. `cyclePower n ℓ` uses the two cyclic directions. The formal definitions include the empty graph, an isolated one-vertex cycle, and a complete two-vertex cycle. They also include powers large enough to give a complete graph.

`Path.lean` and `PathCounts.lean` prove the correspondence with endpoint-bounded positive gaps. `Cycle.lean` and `CycleCounts.lean` prove the cyclic pointing identity. These results connect actual graph counts to polynomial coefficients.

`Sequences.lean` proves the finite convolution inequalities. `ConditionalSequences.lean`, `MonotoneRatios.lean`, and `Euler.lean` give the coefficient comparisons. `GraphCounts.lean` proves the boundary and normalization results. `PathTheorem.lean`, `CycleTheorem.lean`, and `Main.lean` assemble the conclusions.

## Scope

The theorem concerns these two graph families. It does not assert ultra-log-concavity for all graphs or real-rootedness of their domination polynomials. Lean checks the formal mathematical statements. It does not establish publication priority or peer review.

`source-checks.json` identifies the checked source files. `verification.log` contains their theorem output. See [README.md](README.md) for reproduction commands.
