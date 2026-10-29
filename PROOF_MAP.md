# Statement and proof map

This map describes the mathematical source. The Lean 4.35.0 candidate is uncompiled.
Earlier verification claims do not certify this candidate.

The manuscript gives the complete written argument. The Lean proof uses ordinary functions and gradients, not a finite interpolation oracle as a public hypothesis.

| Claim | Formal declaration and scope |
| --- | --- |
| Actual-function upper bound | `THGStrong.taylor_hendrickx_glineur_conjecture3`: every complete real inner-product space; `StrongConvexOn Set.univ μ f`; `HasGradientAt f (g z) z` at every point; pairwise L-Lipschitz gradient; an actual global minimizer; the GD recurrence through N steps; L > 0, 0 ≤ μ ≤ L, 0 ≤ h ≤ 2, every natural N. |
| Radius corollary | `THGStrong.taylor_hendrickx_glineur_conjecture3_with_radius` replaces the initial distance by any upper bound R. |
| Rate | `THGStrong.gradientRate` is exactly the maximum of the rational progress expression (with a separate μ = 0 branch) and the quadratic oscillation factor. |
| Balanced certificate | `THGStrong.balanced_history_bound` constructs every weight and discharges all sign, recurrence, mixed-coefficient, and diagonal-coefficient conditions for every horizon. Its auxiliary curvature can be negative. |
| Progress reduction | `THGStrong.lower_branch_joint` retains the joint terminal potential and the interpolation surplus under scaling. |
| Oscillation reduction | `THGStrong.upper_branch_gradient` lowers auxiliary curvature, possibly below zero. It uses terminal estimates from the actual nonnegative-curvature function. |
| Actual attainment | `THGStrong.Sharpness.attain_rate` constructs actual functions f,g: ℝ → ℝ and a GD sequence. It proves strong convexity, the gradient relation everywhere, gradient Lipschitz continuity, a global minimizer at zero, initial point one, and final norm equal to the claimed rate. It covers every κ ∈ [0,1], h ∈ [0,2], and natural N at L = R = 1. |
| General-scale sharpness | Manuscript Section 7 rescales the normalized witness by F(x) = LR² f(x/R), for L > 0 and R > 0. This step is written mathematics, not a separate checked Lean declaration. |

The boundaries N = 0, h = 0, h = 2, μ = 0, μ = L, and 1 − μh/L = 0 are included. `THGStrong.gradient_of_equal_curvature` handles μ = L directly. `THGStrong.interpolated_gradient_rate_closed` handles the step and horizon endpoints. `THGStrong.Sharpness.nonpositive_affine_rate_dominated` controls negative or zero affine factors. No numerical certificate is used to replace a universal horizon argument.

Only `propext`, `Classical.choice`, and `Quot.sound` are allowed in the transitive axiom reports. These are ordinary Lean/Mathlib foundations; the package is not described as axiom-free.
