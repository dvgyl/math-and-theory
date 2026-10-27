# Order-six theorem map

Let `w : Fin 6 → ℝ` have nonnegative entries. Define the circulant matrix by
`C i j = w (j - i)`, where the indices are taken modulo six. The permanent
`per(C)` is the sum of the products selected by all row-to-column permutations.
Unlike the determinant, this sum has no alternating signs.

Choose any permutation that sorts the six weights. Let `S` be the sum of the
twelfth powers of the five consecutive differences in this sorted list.
Zero weights and equal weights are included.

The main inequalities are

```text
324 per(C)^2 - 5 per(CCᵀ) ≥ 296 S,
1296 per(C)^2 - 5 [per(CCᵀ) + per(CᵀC) + 2 per(C²)] ≥ 1184 S.
```

Thus both left sides are nonnegative. Each left side is zero if and only if
all six weights are equal. If `C` is doubly stochastic, its entries are
nonnegative and each row and column has sum one. In that case, equality in
Gyires's inequality holds if and only if every entry is `1/6`.

The coefficient `296` in the first margin is sharp. The weights
`(0,0,0,0,1,1)` give `S = 1` and a first deficit of `296`. The normalized
weights `(0,0,0,0,1/2,1/2)` prove the same sharpness within the doubly
stochastic class.

The following declarations use the namespace
`MathAndTheory.Gyires.CirculantSix`.

| Result | Declaration | Source |
|---|---|---|
| First margin for sorted weights | `sorted_margin` | [SixPrincipal.lean](sources/SixPrincipal.lean) |
| Combined Gyires margin | `sorted_gyires_margin` | [SixPrincipal.lean](sources/SixPrincipal.lean) |
| Strong inequality | `strong_inequality` | [SixPrincipal.lean](sources/SixPrincipal.lean) |
| Strong equality condition | `strong_equality` | [SixPrincipal.lean](sources/SixPrincipal.lean) |
| Gyires inequality | `gyires` | [SixPrincipal.lean](sources/SixPrincipal.lean) |
| Gyires equality condition | `gyires_equality` | [SixPrincipal.lean](sources/SixPrincipal.lean) |
| Doubly stochastic inequality and equality | `gyires_doubly_stochastic` | [SixPrincipal.lean](sources/SixPrincipal.lean) |
| Sharp coefficient | `margin_coefficient_le` | [SixSharpness.lean](sources/SixSharpness.lean) |
| Sharp coefficient for doubly stochastic matrices | `normalized_margin_coefficient_le` | [SixNormalizedSharpness.lean](sources/SixNormalizedSharpness.lean) |

The proof covers all 720 orderings through 60 affine chamber representatives.
The polynomial identities and coefficient checks are proved in Lean.
[SixTheoremChecks.lean](sources/SixTheoremChecks.lean) restates the principal
matrix conclusions and reports the axioms of ten named theorems.

Use the [reproduction guide](README.md) to check the full source set.
The source manifest lists all 3,091 local modules, their hashes, their imports,
and the pinned external package revisions.
