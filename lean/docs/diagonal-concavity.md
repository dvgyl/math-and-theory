# Diagonal concavity formalization

This family gives a complete classification for `f_M=1+Mσ_1+σ_2+Mσ_3+σ_4` on the positive orthant in four variables. For every `M>0`, diagonal fourth-root concavity is equivalent to `M≥1`. Full fourth-root concavity is equivalent to `M=1`.

Read the [paper](../../preprints/diagonal-concavity/paper.pdf), [source and prior-work guide](../../preprints/diagonal-concavity/README.md), or [verification guide](../../verification/diagonal-concavity/README.md).

## Modules and statements

The proof is [Mathematics/DiagonalConcavity.lean](../MathAndTheory/Mathematics/DiagonalConcavity.lean). Its namespace is `MathAndTheory.DiagonalConcavity`. The principal theorem is `complete_classification`.

The independent [Challenge](../Challenges/DiagonalConcavity.lean) and matching [Solution](../Solutions/DiagonalConcavity.lean) use the theorem `ConcavityChallenge.result`. It states both equivalences for every real `M>0`. The Challenge imports only Mathlib and states the mathematical definitions directly. Its permitted theorem hole is a specification. The [Comparator configuration](../comparator/diagonal-concavity.json) selects the matching Solution statement.

## Source correspondence

[Lachaume's Conjecture 1](https://arxiv.org/html/1712.10327v1) concerns a nonnegative linear combination of unnormalized elementary symmetric polynomials. It asks whether concavity after the `1/p` power on the positive diagonal implies the same property on the positive orthant.

Here `n=p=4`, and the coefficient vector is `(1,M,1,M,1)`. Every coefficient is positive for the stated domain `M>0`.

- `V4` is `Fin 4 → ℝ`.
- `positiveOrthant` is `{x | ∀ i, 0 < x i}`.
- `fourthRoot a` is real exponentiation `a^(1/4)`.
- `family` uses explicit elementary symmetric sums.
- `elementary` uses Mathlib's `Multiset.esymm`.
- `family_eq_elementary` proves that the coordinate formulas are the canonical elementary symmetric functions.

The conclusion uses Mathlib's actual `ConcaveOn` predicate. It does not replace analytic concavity with an assumed polynomial sign test. Positivity of the family on the required domain is proved.

## Theorem map

All declarations in this table are in `MathAndTheory.DiagonalConcavity`.

| Paper claim | Declaration |
| --- | --- |
| Diagonal restriction | `family_diagonal` |
| Diagonal polynomial and its derivatives | `diagonal`, `diagonalD1`, `diagonalD2`, `diagonal_hasDerivAt`, `diagonalD1_hasDerivAt` |
| Exact diagonal curvature identity | `diagonal_curvature_identity` |
| Fourth-root derivative formulas | `fourthRoot_hasDerivAt`, `rootD1_hasDerivAt` |
| Diagonal classification | `diagonal_concave_iff` |
| Positive test line and its polynomial | `witnessLine_positive`, `family_witnessLine` |
| Positive curvature for `M>1` | `line_curvature_identity`, `positive_line_curvature`, `positive_directional_second_derivative` |
| Failure of full concavity for `M>1` | `family_not_concave_of_one_lt` |
| Geometric-mean concavity | `geom4_amgm`, `geom4_concave` |
| Product formula and concavity at `M=1` | `family_one_product`, `family_one_concave` |
| Full-domain classification | `family_concave_iff` |
| Both classifications | `complete_classification` |
| Canonical symmetric-function correspondence | `elementary_zero` through `elementary_four`, `family_eq_elementary` |
| Canonical counterexample at `M=2` | `elementary_symmetric_counterexample` |
| Rational midpoint certificate | `points_midpoint`, `family_pointMinus`, `family_pointCenter`, `family_pointPlus`, `midpoint_strict_violation` |

The diagonal curvature numerator factors as `48(M²−1)(t²−1)²`. On the test line through `(2,2,1/2,1/2)` in direction `(2,2,1,1)`, the fourth-root curvature numerator at zero is `(M−1)(53M+55)`. These identities prove the negative cases. The positive case at `M=1` uses the product `∏(1+x_i)` and a proved geometric-mean inequality.

The geometric-mean result supports the proof. The principal result is the degree-four failure of diagonal testing and its complete one-parameter classification. It is not the degree-two square-root criterion in Lachaume's Theorem 3.3.

## Formal scope

The proof and Solution compile with the pinned Lean 4.35.0 project. The selected theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`. The proof does not need a separate formal statement for the full displayed Hessian matrix; it proves the required directional derivative directly.

This result does not classify arbitrary coefficients or higher dimensions. See the [central verification record](../../verification/README.md) for Comparator and review status. The linked records identify the checked sources and review scope.
