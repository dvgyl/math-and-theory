# Formal proofs of structured Gyires inequalities

The order-five library root is `MathAndTheory.Mathematics.GyiresCirculant5.Main`. Its mathematical declarations use the namespace `MathAndTheory.GyiresCirculant5`. The development uses Lean 4.35.0 and Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`.

The source library defines `circ w i j = w (j - i)`. Mathlib defines `Matrix.circulant w i j = w (i - j)`. The two matrices are transposes. `MathlibStatements.lean` proves the translation used by the Challenge and Solution. The Challenge uses Mathlib's actual matrix, permanent, circulant, and doubly stochastic definitions.

| Statement | Principal declarations |
|---|---|
| Ratio inequality and positive denominator | `gyires_ratio`, `gyires_denominator_pos` |
| Ratio equality only at the uniform matrix | `gyires_ratio_eq_iff` |
| Homogeneous inequality and equality | `gyires_homogeneous`, `gyires_homogeneous_eq_iff` |
| Strong Gram inequality and equality | `strong_inequality`, `strong_inequality_eq_iff` |
| Sorted-gap margin 484, attainment, and optimality | `strong_margin`, `strong_margin_attained`, `strong_margin_sharp` |

The principal declarations are in `Solutions/GyiresCirculant5.lean`. The matching Challenge is `Challenges/GyiresCirculant5.lean`. Only the Challenge contains proof placeholders. The Comparator configuration is `comparator/gyires-circulant-five.json`.

The proof reduces all weight orderings to six affine representatives. It expands the strong deficit in sorted gaps. The `Coefficients` modules prove the integer polynomial identities with `ring` and their signs with `positivity`. They do not use `native_decide`. The equality proof uses the positive pure-gap terms. The witness `(1,1,0,0,0)` proves that 484 is optimal.

From `lean/`, build this family with:

```sh
lake build +MathAndTheory.Mathematics.GyiresCirculant5.Main +Challenges.GyiresCirculant5 +Solutions.GyiresCirculant5
lake env lean -j1 ../verification/gyires-circulant-five/AxiomAudit.lean
```

See [the verification record](../../verification/gyires-circulant-five/README.md) for the exact check results. The coefficient counts in the manuscript are checked separately by integer computation. The principal inequalities, equality cases, and sharp margin have Lean proofs.

The library's `PROVENANCE.md` and `LICENSE` preserve the original source and license. `PermanentGram.lean` retains the Chris Ozols attribution.

## Four-block matrices in every dimension

The library root is `MathAndTheory.Mathematics.Gyires.FourBlock`. Its hypotheses count actual distinct row vectors and column vectors. The matrix must be doubly stochastic. Both counts must be at most two.

The theorem proves `per(AAᵀ) ≤ per(A)`, `per(AᵀA) ≤ per(A)`, and `per(A²) ≤ per(A)`. It also proves the margin `4 per(A)(per(A) - n!/n^n)`, its nonnegativity, Gyires's inequality, and equality exactly at the uniform matrix. The formal statements permit unequal class sizes, zero entries, one row or column type, and orders zero and one.

| Statement | Declaration in `MathAndTheory.GyiresFourBlock` |
|---|---|
| Three contractions | `contractions` |
| Lower bound for the deficit and its nonnegativity | `margin` |
| Gyires's inequality | `gyires` |
| Equality exactly at the uniform matrix | `gyires_eq_iff` |

The independent specifications are in `Challenges/GyiresCirculant5.lean`. The matching proofs are in `Solutions/GyiresFourBlock.lean`. The family Comparator configuration selects these four declarations, ten order-five declarations, and four exceptional-vector declarations. Only the Challenge specifications contain proof placeholders.

The supporting declarations use the namespace `MathAndTheory.Gyires.Bernoulli`. `BernoulliMaximizer` proves the fixed-mean maximizer and adjacent probability bounds. `BernoulliLikelihood` proves the central likelihood bound, the squared likelihood norm bound, and the equality case of the central lower bound. `TwoColumnContraction` connects the probabilities to actual matrix permanents by a permutation average. This proof route does not require a formal proof of each intermediate coefficient identity in the manuscript.

The four-block theorem does not prove the general rank-two theorem. Equality in one contraction does not force a uniform matrix. Deterministic probability laws can attain the scalar norm bound.

## One exceptional column or row

The library root is `MathAndTheory.Mathematics.Gyires.ExceptionalVector`. The matrix has order n ≥ 2 and is doubly stochastic. All columns except one are identical, or all rows except one are identical. The exceptional vector can have any number of distinct entries. Zero entries are permitted.

The theorem proves both bounds `(n! / n^n) per(AAᵀ) ≤ per(A)²` and `(n! / n^n) per(AᵀA) ≤ per(A)²`. Equality in either bound holds exactly at the uniform matrix. It also proves Gyires's inequality for the original matrix product `A²`, with equality exactly at the uniform matrix.

| Statement | Declaration in `MathAndTheory.GyiresExceptional` |
|---|---|
| Both strong Gram bounds | `strong` |
| Equality in each Gram bound | `gram_eq_iff` |
| Gyires's inequality | `gyires` |
| Equality exactly at the uniform matrix | `gyires_eq_iff` |

The independent specifications are in `Challenges/GyiresCirculant5.lean`. The proofs are in `Solutions/GyiresExceptional.lean`. The scalar proof separates two ranges of the second moment of the Bernoulli parameters. It proves the lower bound for the one-success probability in both ranges, including deterministic parameters. Exact coefficient identities connect that probability to the actual matrix permanents.

`ExceptionalBoundaryChecks` includes a matrix with three distinct rows, zero entries, both variance ranges, a deterministic parameter vector, transposition, and arbitrary order-two matrices. Orders zero and one are covered separately by the four-block theorem. This result does not prove the general rank-two theorem.

## General supporting results

The modules in `MathAndTheory.Mathematics.Gyires` contain additional results for arbitrary finite dimensions. They are included in the whole-library axiom audit.

- `PermanentCauchySchwarz` proves the squared and absolute-value permanent Cauchy–Schwarz inequalities. It also gives strict and non-strict matrix-square bounds from two Gram bounds.
- `PermanentPermutation` proves preservation of the permanent and both strong Gram bounds under independent row and column permutations. The resulting Gyires bound uses the square of the permuted matrix.
- `DimensionConstant` proves the comparison of `n! / n^n` with the product of the constants for positive block sizes. The comparison is strict for at least two blocks.
- `BlockPermanent` proves the permanent product identity, both strong bounds, and Gyires closure for finite block sums. It permits unequal sizes and independent row and column permutations. The bounds are strict for at least two positive-dimensional doubly stochastic blocks.

- `CirculantCertificate` proves an exact reduction from nonnegative integer polynomial coefficients to the strong and combined Gyires bounds for circulants. It proves complete sorted-gap representation, matrix evaluation, normality, and affine invariance. Its coefficient-sign hypotheses remain unproved for the higher-order families.

These results support the broader manuscript arguments. The rank-two theorem has a complete Lean proof for orders 2 through 6. The principal order-seven theorem and rank-two orders 7 through 15 remain incomplete in Lean. Separate Lean packages prove the principal order-six and all-order permutation-polynomial theorems.

## Separate formal packages

The [order-six package](../../verification/gyires-circulant-six/README.md) proves the actual circulant matrix inequality, sharp margins 296 and 1184, equality cases, and sharpness witnesses. Its proof covers all 60 affine sorting regions.

The [permutation-polynomial package](../../verification/gyires-permutation-polynomial/README.md) proves both Gram bounds, the matrix-square bound, and Gyires’s inequality for `A = aI + bQ + cQ²`. Here `Q` is any finite permutation matrix and all three coefficients are nonnegative. Orders zero, one, and two and zero coefficients are included. No row-sum normalization is required.


## Rank-two matrices in orders two through six

The [rank-two package](../../verification/gyires-rank-two/README.md) proves the theorem for every real doubly stochastic matrix of rank at most two in orders 2 through 6. Zero entries are allowed. The declaration `MathAndTheory.Gyires.RankTwo.rank_two_complete` uses actual matrix rank and doubly stochastic membership. It has no factorization or certificate hypothesis.

The result includes both Gram contractions, the square contraction, the nonnegative Gyires margin, the normalized left Gram bound, the combined inequality, and equality exactly at the uniform matrix. Its 92 source modules connect the rank representation and convex reduction to complete kernel checks for each required profile. The broader written result through order fifteen remains outside this package's formal range.

Run the package's `check_package.py` for source integrity and `test_verify.py` for verifier failure controls. Its `verify.py` compiles the complete source closure under the pinned Lean and Mathlib versions.
