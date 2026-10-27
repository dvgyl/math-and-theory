# Theorem map

The main declarations use the namespace `MathAndTheory.Gyires.PermutationComplete`. Their source is [PermutationComplete.lean](src/PermutationComplete.lean).

| Result | Declaration |
|---|---|
| Both Gram bounds for every canonical cycle order | `cycle_all_gram_bounds` |
| Both Gram bounds for every finite permutation | `permutation_polynomial_gram_bounds` |
| The bound for the original matrix square A² | `permutation_polynomial_square_bound` |
| The combined Gyires inequality | `permutation_polynomial_gyires_bound` |
| Strict square bound for a cycle of order at least 23 | `cycle_strict_square_bound` |
| Strict combined bound for a cycle of order at least 23 | `cycle_strict_gyires_bound` |

The last two statements require at least one positive weight. Every statement requires nonnegative a,b,c. The arbitrary-permutation statements use any finite index type and any permutation of that type.

[CompleteAudit.lean](src/CompleteAudit.lean) restates four conclusions with the actual matrix A=aI+bQ+cQ² and the explicit constant n!/n^n. These declarations use `MathAndTheory.Gyires.PermutationCompleteAudit`:

- `actual_permutation_polynomial_gram_bounds`.
- `actual_permutation_polynomial_square_bound`.
- `actual_permutation_polynomial_gyires_bound`.
- `actual_cycle_strict_gyires_bound`.

The proof components are as follows.

| Component | Source and result |
|---|---|
| Matrix definition and Gram product | `OffsetExpansion.lean`, `PermutationGramExpansion.lean` |
| Cyclic permanent formula | `BalancedWalks.lean`, `cycle_permanent_formula` |
| Positive-root lower bound | `RootBound.lean`, `cycle_weightScale_lower_bound` |
| Actual Gram transfer formula | `GramTrace16.lean`, `TransferBlocks.lean` |
| Weighted trace inequality | `WeightedTrace.lean`, `trace_power_bound` |
| Six-state weighted bound | `WeightedComparison.lean`, `transferTwo_weighted_comparison` |
| Exact threshold and all larger orders | `TwentyThreeTail.lean`, `CycleTailTwentyThree.lean` |
| Orders zero through two | `SmallCycleBounds.lean`, `cycle_small_order_both_gram` |
| Finite polynomial identities | `PrototypeCoverage.lean`, `OrderFourGap.lean`, `GapFive.lean`, `GapSix.lean`, and `Gap007.lean` through `Gap022.lean` |
| Arbitrary cycle structure | `OrbitDecomposition.lean`, `BlockClosure.lean`, `CycleAssembly.lean` |
| Comparison for A² | `PermanentCauchySchwarz.lean`, `permanent_square_bound_of_gram_bounds` |

For orders 3–22, the three gap assignments and their reflections cover every nonnegative real triple. The coefficient identities are equalities with the actual permanent expressions. Their nonnegative coefficients give the inequalities on whole closed parameter regions. Numerical samples are not used as a proof.

For n≥23, the normalized transfer estimate is

    2+8·2^n+39(169/70)^(n−4).

Its product with n!/n^n is strictly less than one. The proof includes both endpoints of the normalized parameter interval and the zero-weight matrix. No spectral diagonalization assumption is required.
