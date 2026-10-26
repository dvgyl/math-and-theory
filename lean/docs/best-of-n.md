# Best-of-n formalization

This family proves a finite disproof of Beirami et al., Conjecture 7.2, and a counterexample for every integer budget at least two with arbitrarily small reference probabilities.

The [paper](../../preprints/best-of-n/paper.pdf) gives the mathematical proof. The [paper guide](../../preprints/best-of-n/README.md) records prior-work evidence and search limits. The [verification guide](../../verification/best-of-n/README.md) gives commands and computational limits.

## Modules and principal statements

| File | Namespace | Main result |
| --- | --- | --- |
| [Finite.lean](../MathAndTheory/TheoreticalCS/BestOfN/Finite.lean) | `MathAndTheory.BestOfN` | `universal_curve_false` |
| [Extension.lean](../MathAndTheory/TheoreticalCS/BestOfN/Extension.lean) | `MathAndTheory.BestOfNExtension` | `every_budget_small_atoms` |
| [Challenge](../Challenges/BestOfN.lean) | `BestOfNChallenge` | Independent definitions and two target statements |
| [Solution](../Solutions/BestOfN.lean) | `BestOfNChallenge` | Proofs of those exact statements |

`BestOfNChallenge.result` states `¬ UniversalCurve`. The second target quantifies over every natural `n≥2` and real `δ>0`. It produces a finite positive normalized law with every probability at most `δ`, win rate in `[1/2,1)`, and divergence below `ell(W)`.

The Challenge imports only Mathlib. Its permitted theorem holes specify the targets. The Solution imports the proved modules. The Challenge and Solution use the same qualified mathematical definitions and theorem types. The [Comparator configuration](../comparator/best-of-n.json) selects both targets.

## Source correspondence

The source is [Beirami et al., Conjecture 7.2](https://arxiv.org/html/2401.01879v3). Equation (28) gives half credit for equality. Lemma 5.2 uses the same cumulative probabilities as this development.

The response set is `Fin k`. Reward is the response index, so rewards are distinct. `before p i` sums masses below `i`; `through p i` also includes `i`. The selected law is

`bestOfN n p i = (through p i)^n − (before p i)^n`.

For independent draws, these powers are the probabilities that every draw is below or at the stated index. Their difference is the probability that the maximum index is exactly `i`. The development represents the law by finite real-valued sums. It does not introduce a separate probability-measure representation.

`winRate` is the half-credit expectation. `kl` is `Σ q_i log(q_i/p_i)`, with the selected law first and natural logarithms. `ell` is the curve in the source. The final finite theorem does not assume that an inverse point exists; it proves that point exists.

## Finite theorem map

The following declarations are in `MathAndTheory.BestOfN`.

| Claim | Declaration |
| --- | --- |
| Reference law and admissibility | `reference`, `reference_positive`, `reference_sum` |
| Exact selected law | `selected_probabilities` |
| Equality with all sixteen independent draw pairs | `selected_equals_independent_sampling` |
| Selected admissibility | `selected_positive`, `selected_sum` |
| Exact win rate and domain | `win_rate_exact`, `win_rate_in_domain` |
| Exact logarithmic divergence and curve | `kl_exact`, `ell_exact` |
| Integer certificate and logarithm bound | `ratio_lower_bound`, `log_ratio_lower_bound` |
| Gap greater than `1/2445` | `gap_positive` |
| Strict disproof | `explicit_counterexample`, `universal_curve_false` |
| Strict monotonicity and inverse-point result | `ell_strictMonoOn`, `inverse_curve_exists`, `inverse_curve_violation` |

## Every-budget theorem map

The following declarations are in `MathAndTheory.BestOfNExtension`. The internal parameter is `r=n−2`. Thus `r+2` is the sampling budget.

| Claim | Declaration |
| --- | --- |
| Entropy and win-rate primitives | `entropyPrimitive`, `winPrimitive` |
| Their exact derivatives | `entropyPrimitive_hasDerivAt`, `winPrimitive_hasDerivAt` |
| Scalar logarithm inequality | `entropy_tangent` |
| Finite interval bounds | `interval_kl_bound`, `interval_win_bound` |
| Convexity and tangent inequality for `ell` | `curveD2_pos`, `curve_convex`, `curve_tangent` |
| Continuous reference values | `baseD`, `baseW`, `lossC`, `curve_base` |
| Strict lower bound `D0>1/6` | `baseD_lower` |
| Atom family and interval masses | `atomFamily`, `grid`, `intervalMass` |
| Exact cumulative sums | `before_cons`, `through_cons`, `before_const`, `through_const` |
| Selected masses | `atomFamily_selected_zero`, `atomFamily_selected_succ` |
| Exact divergence and win-rate sums | `atomFamily_kl`, `atomFamily_win` |
| Telescoping identities | `sum_telescope`, `intervalMass_sum` |
| Reference and selected normalization | `atomFamily_sum`, `atomFamily_selected_sum` |
| Finite divergence and win-rate bounds | `atomFamily_kl_le`, `atomFamily_win_lower`, `atomFamily_win_lt_one` |
| Slope and coefficient bounds | `slope_base_bounds`, `lossC_bounds`, `baseW_lower` |
| Parameter bounds, atom cap, domain, and strict gap | `finite_construction` |
| Complete quantified theorem | `every_budget_small_atoms` |

The construction chooses `a=min(δ,1/(8(n+1)))`, `T=a^n/(48(n+1))`, an integer `m>(1−a)/T`, and `h=(1−a)/m`. The reference law is `(a,h,…,h)`. Its finite sums use differentiable primitives and telescope. No unproved limit, Jensen inequality, or discretization hypothesis appears in the theorem.

Within `finite_construction`, the local proof `hgap` establishes `ell(W)−D>3a^n/32`. The proof also checks `a≤1/24`, `a^n≤a`, `a^(n+1)≤a`, `h≤1/144`, and `h≤a`. These bounds imply the required win-rate domain and probability cap.

## Formal scope

The modules compile with the pinned Lean 4.35.0 project. The selected Solution statements depend only on `propext`, `Classical.choice`, and `Quot.sound`. Compilation and axiom inspection do not establish novelty or expert validation. See the [central verification record](../../verification/README.md) for Comparator and review status. This guide does not claim that final review has occurred.
