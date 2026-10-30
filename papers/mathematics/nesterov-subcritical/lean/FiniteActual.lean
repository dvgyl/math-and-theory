import FiniteExcursion
import MoreauTrajectory
import ExponentSelection

set_option autoImplicit false

noncomputable section
open Set
open NesterovThresholdModel

namespace NesterovThreshold

/-- Quantitative excursions for the literal, globally C1,1 Moreau-gradient ODE.
The parameter is selected before the trajectory. Every trajectory with the stated
zero-velocity initialization crosses the bound and has a nondecreasing first
coordinate. No auxiliary energy inequality is assumed in this statement. -/
theorem exists_parameter_actual_excursion (e : PowerExponent) {r M : ℝ}
    (hr : 1 < r) (hpr : e.p * (r - 1) ≤ 2) (hM : 2 ≤ M) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      ∀ q u : ℝ → Plane,
        ContinuousOn q (Ici 0) → ContinuousOn u (Ici 0) →
        (∀ t > 0, HasDerivAt q (u t) t) →
        (∀ t > 0, HasDerivAt u (-(r / t) • u t - gradient e ε (q t)) t) →
        q 0 = point 2 1 → u 0 = 0 →
        (∃ t : ℝ, 0 ≤ t ∧ M < q t 0) ∧
          MonotoneOn (fun t => q t 0) (Ici 0) := by
  obtain ⟨ε, he, he1, hε⟩ := exists_parameter_excursion hr e.p_gt_one e.p_le_two hpr hM
  refine ⟨ε, he, he1, ?_⟩
  intro q u hq hu hqd hud hq0 hu0
  let S := ValleyPath.ofVector e he he1 q u hq hu hqd hud hq0 hu0
  exact ⟨hε S, S.first_coordinate_monotone hr⟩

/-- A single even dual exponent supplies arbitrarily large permanent excursions
for every damping parameter strictly between one and three. -/
theorem exists_exponent_all_excursions {r : ℝ} (hr : 1 < r) (hr3 : r < 3) :
    ∃ e : PowerExponent, ∀ M : ℝ, 2 ≤ M →
      ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
        ∀ q u : ℝ → Plane,
          ContinuousOn q (Ici 0) → ContinuousOn u (Ici 0) →
          (∀ t > 0, HasDerivAt q (u t) t) →
          (∀ t > 0, HasDerivAt u (-(r / t) • u t - gradient e ε (q t)) t) →
          q 0 = point 2 1 → u 0 = 0 →
          (∃ t : ℝ, 0 ≤ t ∧ M < q t 0) ∧
            MonotoneOn (fun t => q t 0) (Ici 0) := by
  obtain ⟨e, he⟩ := exists_powerExponent hr3
  exact ⟨e, fun M hM => exists_parameter_actual_excursion e hr he hM⟩

#print axioms exists_parameter_actual_excursion
#print axioms exists_exponent_all_excursions

end NesterovThreshold
