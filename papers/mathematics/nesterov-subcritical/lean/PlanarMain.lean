import GeneralVolterraCalculus
import PlanarTrajectory

/-!
Headline theorem for the planar Huber valley with damping `1 < r ≤ 2`:
global existence of an actual zero-initial-velocity solution (general-`r`
weighted Volterra fixed point) and escape to infinity.
-/

set_option autoImplicit false

noncomputable section
open Set Filter
open scoped Topology

namespace NesterovPlanar

/-- Existence and escape of an actual globally defined, zero-initial-velocity
solution for every damping `1 < r ≤ 2`. The singular initial time is handled by
the general-`r` global Volterra fixed point, not by assuming an ODE solution. -/
theorem exists_planar_escaping_trajectory {r : ℝ} (hr : 1 < r) (hr2 : r ≤ 2) :
    ∃ q u : ℝ → NesterovModel.Plane,
      Continuous q ∧ Continuous u ∧
      q 0 = NesterovModel.point 2 1 ∧ u 0 = 0 ∧
      HasDerivAt q 0 0 ∧
      (∀ t : ℝ, 0 ≤ t → HasDerivAt q (u t) t) ∧
      (∀ t : ℝ, 0 < t →
        HasDerivAt u (-(r / t) • u t - NesterovModel.gradient (q t)) t) ∧
      Tendsto (fun t => q t 0) atTop atTop ∧
      Tendsto (fun t => ‖q t‖) atTop atTop := by
  obtain ⟨q, u, hqc, huc, hq0, hu0, hqd, hud⟩ :=
    GeneralNesterovExistence.exists_global_nesterov hr NesterovModel.gradient
      NesterovModel.gradient_lipschitz NesterovModel.gradient_norm_le_two
      (NesterovModel.point 2 1)
  have hescape := every_planar_trajectory_escapes hr hr2 q u hqc.continuousOn huc.continuousOn
    (fun t ht => hqd t ht.le) hud hq0 hu0
  refine ⟨q, u, hqc, huc, hq0, hu0, ?_, hqd, hud, hescape.1, hescape.2⟩
  simpa only [hu0] using hqd 0 le_rfl

/-- The explicit planar counterexample for every damping `1 < r ≤ 2`: the
same global objective, gradient, smoothness and complete minimizer ray as in
the damping-two theorem, the initial condition `q(0) = (2, 1)`, `q'(0) = 0`,
the actual damping-`r` ODE, global existence, and escape to infinity. -/
theorem planar_valley_escape {r : ℝ} (hr : 1 < r) (hr2 : r ≤ 2) :
    (∀ z : NesterovModel.Plane,
      NesterovModel.potential z =
        (if ‖z‖ ≤ 1 then (‖z‖ ^ 2 + 1) / 2 else ‖z‖) - z 0) ∧
    ConvexOn ℝ Set.univ NesterovModel.potential ∧
    Differentiable ℝ NesterovModel.potential ∧
    (∀ z : NesterovModel.Plane,
      HasGradientAt NesterovModel.potential (NesterovModel.gradient z) z) ∧
    LipschitzWith 1 NesterovModel.gradient ∧
    (∀ z : NesterovModel.Plane, 0 ≤ NesterovModel.potential z) ∧
    (∀ z : NesterovModel.Plane,
      NesterovModel.potential z = 0 ↔ z 1 = 0 ∧ 1 ≤ z 0) ∧
    ∃ q u : ℝ → NesterovModel.Plane,
      Continuous q ∧ Continuous u ∧
      q 0 = NesterovModel.point 2 1 ∧ u 0 = 0 ∧
      HasDerivAt q 0 0 ∧
      (∀ t : ℝ, 0 ≤ t → HasDerivAt q (u t) t) ∧
      (∀ t : ℝ, 0 < t →
        HasDerivAt u (-(r / t) • u t - NesterovModel.gradient (q t)) t) ∧
      Tendsto (fun t => q t 0) atTop atTop ∧
      Tendsto (fun t => ‖q t‖) atTop atTop := by
  exact ⟨NesterovModel.potential_formula, NesterovModel.potential_convex,
    NesterovModel.potential_differentiable, NesterovModel.potential_hasGradientAt,
    NesterovModel.gradient_lipschitz, NesterovModel.potential_nonneg,
    NesterovModel.potential_eq_zero_iff, exists_planar_escaping_trajectory hr hr2⟩

end NesterovPlanar
