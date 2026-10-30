import PlanarEnergy
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
Invariants of the actual damping-`r` scalar system for the globally defined
Huber-norm valley, with zero initial velocity at the singular time `t = 0`.
-/

set_option autoImplicit false

noncomputable section
open Set Filter
open scoped Topology

namespace NesterovPlanar

/-- The actual damping-`r` scalar system for the globally defined Huber-norm
potential, including its zero-velocity initial condition. Existence is proved
in the separate global ODE construction, not assumed. -/
structure PlanarTrajectory (r : ℝ) where
  x : ℝ → ℝ
  y : ℝ → ℝ
  v : ℝ → ℝ
  w : ℝ → ℝ
  cont_x : ContinuousOn x (Ici 0)
  cont_y : ContinuousOn y (Ici 0)
  cont_v : ContinuousOn v (Ici 0)
  cont_w : ContinuousOn w (Ici 0)
  deriv_x : ∀ t > 0, HasDerivAt x (v t) t
  deriv_y : ∀ t > 0, HasDerivAt y (w t) t
  deriv_v : ∀ t > 0, HasDerivAt v
    (-r / t * v t + 1 - x t / max 1 (radius (x t) (y t))) t
  deriv_w : ∀ t > 0, HasDerivAt w
    (-r / t * w t - y t / max 1 (radius (x t) (y t))) t
  initial_x : x 0 = 2
  initial_y : y 0 = 1
  initial_v : v 0 = 0
  initial_w : w 0 = 0

lemma outward_force_nonneg (x y : ℝ) : 0 ≤ 1 - x / max 1 (radius x y) := by
  have hd : 0 < max 1 (radius x y) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hx : x ≤ max 1 (radius x y) := (x_le_radius x y).trans (le_max_right _ _)
  exact sub_nonneg.mpr ((div_le_one hd).mpr hx)

namespace PlanarTrajectory

variable {r : ℝ} (S : PlanarTrajectory r)

/-- `(t^r v)' = t^r (1 - x / max 1 R) ≥ 0` and `t^r v → 0` at `t = 0`. -/
theorem velocity_nonneg (hr : 0 < r) : ∀ t ≥ 0, 0 ≤ S.v t := by
  have hdq : ∀ t > 0, HasDerivAt (fun s => s ^ r * S.v s)
      (t ^ r * (1 - S.x t / max 1 (radius (S.x t) (S.y t)))) t := by
    intro t ht
    have e1 : t ^ (r - 1) = t ^ r / t := Real.rpow_sub_one ht.ne' r
    convert (Real.hasDerivAt_rpow_const (p := r) (Or.inl ht.ne')).mul (S.deriv_v t ht) using 1
    rw [e1]
    ring
  have hq : ContinuousOn (fun s => s ^ r * S.v s) (Ici 0) :=
    (Real.continuous_rpow_const hr.le).continuousOn.mul S.cont_v
  have hmono : MonotoneOn (fun s => s ^ r * S.v s) (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (0 : ℝ)) hq
    · intro t ht
      exact (hdq t (by simpa only [interior_Ici, mem_Ioi] using ht)).hasDerivWithinAt
    · intro t ht
      have ht0 : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
      exact mul_nonneg (Real.rpow_pos_of_pos ht0 r).le (outward_force_nonneg (S.x t) (S.y t))
  intro t ht
  rcases eq_or_lt_of_le ht with ht0 | ht0
  · simp [← ht0, S.initial_v]
  · have hm := hmono (by simp : (0 : ℝ) ∈ Ici 0) ht ht
    simp only [Real.zero_rpow hr.ne', zero_mul] at hm
    exact nonneg_of_mul_nonneg_right hm (Real.rpow_pos_of_pos ht0 r)

theorem first_coordinate_monotone (hr : 0 < r) : MonotoneOn S.x (Ici 0) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (0 : ℝ)) S.cont_x
  · intro t ht
    exact (S.deriv_x t (by simpa only [interior_Ici, mem_Ioi] using ht)).hasDerivWithinAt
  · intro t ht
    have ht0 : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
    exact S.velocity_nonneg hr t ht0.le

theorem first_coordinate_ge_two (hr : 0 < r) : ∀ t ≥ 0, 2 ≤ S.x t := by
  intro t ht
  simpa only [S.initial_x] using S.first_coordinate_monotone hr (by simp) ht ht

lemma denominator_eq_radius (hr : 0 < r) {t : ℝ} (ht : 0 ≤ t) :
    max 1 (radius (S.x t) (S.y t)) = radius (S.x t) (S.y t) := by
  apply max_eq_right
  linarith [S.first_coordinate_ge_two hr t ht, x_le_radius (S.x t) (S.y t)]

theorem exterior_deriv_v (hr : 0 < r) {t : ℝ} (ht : 0 < t) :
    HasDerivAt S.v (-r / t * S.v t +
      potential (S.x t) (S.y t) / radius (S.x t) (S.y t)) t := by
  have hR : radius (S.x t) (S.y t) ≠ 0 := by
    have := (S.first_coordinate_ge_two hr t ht.le).trans (x_le_radius (S.x t) (S.y t))
    linarith
  convert S.deriv_v t ht using 1
  rw [S.denominator_eq_radius hr ht.le]
  unfold potential
  field_simp
  ring

theorem exterior_deriv_w (hr : 0 < r) {t : ℝ} (ht : 0 < t) :
    HasDerivAt S.w (-r / t * S.w t - S.y t / radius (S.x t) (S.y t)) t := by
  simpa only [S.denominator_eq_radius hr ht.le] using S.deriv_w t ht

def totalEnergy (t : ℝ) : ℝ := S.v t ^ 2 / 2 + transverseEnergy (S.x t) (S.y t) (S.w t)

lemma continuousOn_totalEnergy : ContinuousOn S.totalEnergy (Ici 0) := by
  have hx := S.cont_x
  have hy := S.cont_y
  have hv := S.cont_v
  have hw := S.cont_w
  unfold totalEnergy transverseEnergy potential radius
  fun_prop

lemma hasDerivAt_totalEnergy (hr : 0 < r) {t : ℝ} (ht : 0 < t) :
    HasDerivAt S.totalEnergy (-r / t * (S.v t ^ 2 + S.w t ^ 2)) t := by
  have hx := S.deriv_x t ht
  have hy := S.deriv_y t ht
  have hw := S.exterior_deriv_w hr ht
  have hW := hasDerivAt_transverseEnergy hx hy hw
    (by linarith [S.first_coordinate_ge_two hr t ht.le])
  convert (((S.exterior_deriv_v hr ht).pow 2).div_const 2).add hW using 1
  simp only [Nat.cast_ofNat, pow_one]
  ring

/-- `A = (v² + w²)/2 + V` is nonincreasing: `A' = -(r/t)(v² + w²)`. -/
theorem totalEnergy_antitone (hr : 0 < r) : AntitoneOn S.totalEnergy (Ici 0) := by
  have hmono : MonotoneOn (fun t => -S.totalEnergy t) (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (0 : ℝ))
      S.continuousOn_totalEnergy.neg
    · intro t ht
      exact ((S.hasDerivAt_totalEnergy hr
        (by simpa only [interior_Ici, mem_Ioi] using ht)).neg).hasDerivWithinAt
    · intro t ht
      have ht0 : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
      have hp : 0 ≤ (r / t) * (S.v t ^ 2 + S.w t ^ 2) :=
        mul_nonneg (div_nonneg hr.le ht0.le) (by positivity)
      convert hp using 1
      ring
  intro a ha b hb hab
  exact neg_le_neg_iff.mp (hmono ha hb hab)

theorem transverseEnergy_le_one (hr : 0 < r) : ∀ t ≥ 0,
    transverseEnergy (S.x t) (S.y t) (S.w t) ≤ 1 := by
  have hzero : S.totalEnergy 0 ≤ 1 := by
    simp only [totalEnergy, transverseEnergy, S.initial_v, S.initial_x, S.initial_y,
      S.initial_w, zero_pow (by decide : 2 ≠ 0), zero_div, zero_add]
    unfold potential
    have hs := radius_sq 2 1
    have hrad := radius_nonneg 2 1
    nlinarith
  intro t ht
  have hT : S.totalEnergy t ≤ 1 :=
    (S.totalEnergy_antitone hr (by simp) ht ht).trans hzero
  unfold totalEnergy at hT
  nlinarith [sq_nonneg (S.v t)]

theorem weightedEnergy_monotone (hr1 : 1 < r) (hr2 : r ≤ 2) :
    MonotoneOn (weightedEnergy r S.x S.y S.w) (Ici 0) :=
  NesterovPlanar.weightedEnergy_monotone hr1.le hr2 S.cont_x S.cont_y S.cont_w
    S.deriv_x S.deriv_y (fun _ ht => S.exterior_deriv_w (by linarith) ht)
    (fun t ht => S.first_coordinate_ge_two (by linarith) t ht.le)
    (fun t ht => S.velocity_nonneg (by linarith) t ht.le)

theorem weightedEnergy_positive_initial (hr1 : 1 < r) :
    0 < weightedEnergy r S.x S.y S.w 0 :=
  initial_weightedEnergy_pos hr1.ne' (by rw [S.initial_y]; norm_num)

end PlanarTrajectory
end NesterovPlanar
