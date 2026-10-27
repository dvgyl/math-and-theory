# Formal proofs of the order-five and four-block Gyires results

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

The standalone specifications are in `Challenges/GyiresFourBlock.lean`. The matching proofs are in `Solutions/GyiresFourBlock.lean`. The existing family Comparator configuration selects these four declarations and the ten order-five declarations. Only the Challenge specifications contain proof placeholders.

The supporting declarations use the namespace `MathAndTheory.Gyires.Bernoulli`. `BernoulliMaximizer` proves the fixed-mean maximizer and adjacent probability bounds. `BernoulliLikelihood` proves the central likelihood bound, the squared likelihood norm bound, and the equality case of the central lower bound. `TwoColumnContraction` connects the probabilities to actual matrix permanents by a permutation average. This proof route does not require a formal proof of each intermediate coefficient identity in the manuscript.

The four-block theorem does not prove the general rank-two theorem. Equality in one contraction does not force a uniform matrix. Deterministic probability laws can attain the scalar norm bound.

## General supporting results

The modules in `MathAndTheory.Mathematics.Gyires` contain additional results for arbitrary finite dimensions. They are included in the whole-library axiom audit.

- `PermanentCauchySchwarz` proves the squared and absolute-value permanent Cauchy–Schwarz inequalities. It also gives strict and non-strict matrix-square bounds from two Gram bounds.
- `PermanentPermutation` proves preservation of the permanent and both strong Gram bounds under independent row and column permutations. The resulting Gyires bound uses the square of the permuted matrix.
- `DimensionConstant` proves the comparison of `n! / n^n` with the product of the constants for positive block sizes. The comparison is strict for at least two blocks.
- `BlockPermanent` proves the permanent product identity, both strong bounds, and Gyires closure for finite block sums. It permits unequal sizes and independent row and column permutations. The bounds are strict for at least two positive-dimensional doubly stochastic blocks.

- `CirculantCertificate` proves an exact reduction from nonnegative integer polynomial coefficients to the strong and combined Gyires bounds for circulants. It proves complete sorted-gap representation, matrix evaluation, normality, and affine invariance. Its coefficient-sign hypotheses remain unproved for the higher-order families.

These results support the broader manuscript arguments. The principal higher-order circulant, permutation-polynomial, exceptional-vector, and finite rank-two theorems remain incomplete in Lean.
