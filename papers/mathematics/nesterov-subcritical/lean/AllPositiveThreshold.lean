import SharpThreshold
import LowDampingHilbert

set_option autoImplicit false

noncomputable section
open Set Filter
open scoped Topology

namespace NesterovSharpThreshold
open NesterovHilbert

/-- Actual norm-divergent examples for every positive damping below three.
The range at most one is the explicit classical scalar construction; the
range strictly between one and three is the new smooth Hilbert construction. -/
theorem exists_positive_subcritical_norm_divergent_flow {r : ℝ}
    (hr : 0 < r) (hr3 : r < 3) :
    ∃ (F : Hilbert → ℝ) (G : Hilbert → Hilbert) (X V : ℝ → Hilbert) (z : Hilbert),
      ConvexOn ℝ univ F ∧
      (∀ x, HasGradientAt F (G x) x) ∧
      LipschitzWith 1 G ∧ (∀ x, ‖G x‖ ≤ 2) ∧
      F z = 0 ∧ (∀ x, 0 ≤ F x) ∧
      Continuous X ∧ Continuous V ∧ V 0 = 0 ∧
      (∀ t ≥ 0, HasDerivAt X (V t) t) ∧
      (∀ t > 0, HasDerivAt V (-(r / t) • V t - G (X t)) t) ∧
      Tendsto (fun t => ‖X t‖) atTop atTop := by
  by_cases hr1 : 1 < r
  · obtain ⟨F, G, X, V, hconv, hgrad, hLip, hbound, hF0, hFpos,
      hX, hV, _hX0, hV0, hXd, hVd, hescape⟩ :=
      exists_subcritical_norm_divergent_flow hr1 hr3
    exact ⟨F, G, X, V, 0, hconv, hgrad, hLip, hbound, hF0, hFpos,
      hX, hV, hV0, hXd, hVd, hescape⟩
  · obtain ⟨F, G, X, V, z, hconv, hgrad, hLip, hbound, hFz, hFpos,
      hX, hV, _hX0, hV0, hXd, hVd, hescape⟩ :=
      exists_low_damping_norm_divergent_flow hr (le_of_not_gt hr1)
    exact ⟨F, G, X, V, z, hconv, hgrad, hLip, hbound, hFz, hFpos,
      hX, hV, hV0, hXd, hVd, hescape⟩

/-- The exact universal boundedness threshold over every positive damping
parameter. All objectives have an attained minimum and a globally
1-Lipschitz actual gradient, all velocities start at zero, and all solutions
are actual global trajectories continuous through the singular initial time. -/
theorem sharp_boundedness_threshold_all_positive {r : ℝ} (hr : 0 < r) :
    UniversalBoundedness r ↔ 3 ≤ r := by
  constructor
  · intro hU
    by_contra hn
    have hr3 : r < 3 := lt_of_not_ge hn
    obtain ⟨F, G, X, V, z, hconv, hgrad, hLip, _hbound, hFz, hFpos,
      hX, hV, hV0, hXd, hVd, hescape⟩ :=
      exists_positive_subcritical_norm_divergent_flow hr hr3
    have hmin : ∃ z, ∀ x, F z ≤ F x := ⟨z, fun x => by rw [hFz]; exact hFpos x⟩
    obtain ⟨C, hC⟩ := hU F G X V hconv hgrad hLip hmin hX hV hV0 hXd hVd
    have hbig : ∀ᶠ t in atTop, C + 1 ≤ ‖X t‖ := (tendsto_atTop.1 hescape) (C + 1)
    obtain ⟨t, ht, hlarge⟩ := ((eventually_ge_atTop (0 : ℝ)).and hbig).exists
    have hsmall := hC t ht
    linarith
  · exact universalBoundedness_of_three_le

#print axioms exists_positive_subcritical_norm_divergent_flow
#print axioms sharp_boundedness_threshold_all_positive

end NesterovSharpThreshold
