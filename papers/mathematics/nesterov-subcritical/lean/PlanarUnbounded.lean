import PlanarInvariants
import EulerObstruction

/-!
Every actual damping-`r` scalar trajectory (`1 < r ≤ 2`) of the Huber-norm
valley with the prescribed zero-velocity initial data has an unbounded, hence
divergent, first coordinate.
-/

set_option autoImplicit false

noncomputable section
open Set Filter
open scoped Topology

namespace NesterovPlanar
namespace PlanarTrajectory

variable {r : ℝ} (S : PlanarTrajectory r)

/-- Every actual scalar trajectory of the globally defined Huber-norm model,
with damping `1 < r ≤ 2` and the prescribed zero-velocity initial condition,
has an unbounded first coordinate. -/
theorem first_coordinate_unbounded (hr1 : 1 < r) (hr2 : r ≤ 2) :
    ¬ ∃ M : ℝ, ∀ t : ℝ, 1 ≤ t → S.x t ≤ M := by
  rintro ⟨M, hM⟩
  have hr0 : 0 < r := by linarith
  have hM2 : 2 ≤ M := (S.first_coordinate_ge_two hr0 1 (by norm_num)).trans (hM 1 le_rfl)
  let A : ℝ := Real.exp (M / 2) * (2 * M + 3)
  have hA : 0 < A := mul_pos (Real.exp_pos _) (by linarith)
  let c : ℝ := weightedEnergy r S.x S.y S.w 0 / A
  have hc : 0 < c := div_pos (S.weightedEnergy_positive_initial hr1) hA
  have hWlower : ∀ t : ℝ, 1 ≤ t → c / t ^ 2 ≤ transverseEnergy (S.x t) (S.y t) (S.w t) := by
    intro t ht
    have ht0 : 0 < t := by linarith
    have hl := S.weightedEnergy_monotone hr1 hr2 (by simp : (0 : ℝ) ∈ Ici 0) ht0.le ht0.le
    have hu := weightedEnergy_upper (w := S.w) (y := S.y) hr1.le hr2 ht
      (S.first_coordinate_ge_two hr0 t ht0.le) (hM t ht)
      (S.transverseEnergy_le_one hr0 t ht0.le)
    have hcprod : c ≤ t ^ 2 * transverseEnergy (S.x t) (S.y t) (S.w t) := by
      apply (div_le_iff₀ hA).mpr
      convert hl.trans hu using 1
      unfold A
      ring
    apply (div_le_iff₀ (sq_pos_of_pos ht0)).mpr
    nlinarith
  let B : ℝ := M + 1
  have hB : 0 < B := by dsimp [B]; linarith
  let H : ℝ → ℝ := fun t => companion B (S.x t) (S.y t)
  let D : ℝ → ℝ := fun t => companionVelocity B (S.v t) (S.y t) (S.w t)
  let DD : ℝ → ℝ := fun t => companionAcceleration r t B (S.x t) (S.y t) (S.v t) (S.w t)
  have hH : ∀ t, 1 ≤ t → HasDerivAt H (D t) t := by
    intro t ht
    exact hasDerivAt_companion (S.deriv_x t (by linarith)) (S.deriv_y t (by linarith))
  have hD : ∀ t, 1 ≤ t → HasDerivAt D (DD t) t := by
    intro t ht
    exact hasDerivAt_companionVelocity (S.deriv_y t (by linarith))
      (S.exterior_deriv_v hr0 (by linarith)) (S.exterior_deriv_w hr0 (by linarith))
  have hforce : ∀ t, 1 ≤ t → (c / (2 * B)) / t ^ 2 ≤ DD t + (r / t) * D t := by
    intro t ht
    have ht0 : 0 ≤ t := by linarith
    calc
      (c / (2 * B)) / t ^ 2 = (c / t ^ 2) / (2 * B) := by ring
      _ ≤ transverseEnergy (S.x t) (S.y t) (S.w t) / (2 * B) :=
        div_le_div_of_nonneg_right (hWlower t ht) (by positivity)
      _ ≤ DD t + (r / t) * D t :=
        companion_drift_lower (S.first_coordinate_ge_two hr0 t ht0)
          (radius_upper (hM t ht) (S.transverseEnergy_le_one hr0 t ht0))
  apply unbounded_of_euler_forcing hr1 (by norm_num : (0:ℝ) < 1)
    (div_pos hc (by positivity : 0 < 2 * B)) hH hD hforce
  refine ⟨M + 1, ?_⟩
  intro t ht
  exact companion_upper (S.first_coordinate_ge_two hr0 t (by linarith)) (hM t ht)
    (S.transverseEnergy_le_one hr0 t (by linarith))

/-- Escape to infinity, rather than only failure to settle at one minimizer. -/
theorem first_coordinate_tendsto_atTop (hr1 : 1 < r) (hr2 : r ≤ 2) :
    Tendsto S.x atTop atTop := by
  have hu := S.first_coordinate_unbounded hr1 hr2
  push_neg at hu
  apply tendsto_atTop_atTop.mpr
  intro b
  obtain ⟨t, ht, hbt⟩ := hu b
  refine ⟨t, ?_⟩
  intro s hs
  exact hbt.le.trans (S.first_coordinate_monotone (by linarith)
    (show t ∈ Ici 0 from by change 0 ≤ t; linarith)
    (show s ∈ Ici 0 from by change 0 ≤ s; linarith) hs)

end PlanarTrajectory
end NesterovPlanar
