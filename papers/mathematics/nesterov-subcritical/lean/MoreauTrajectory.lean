import PowerValley
import ValleyPath

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Set
open NesterovThresholdModel

namespace NesterovThreshold

lemma hasDerivAt_coordinate {q : ℝ → Plane} {q' : Plane} {t : ℝ}
    (h : HasDerivAt q q' t) (i : Fin 2) :
    HasDerivAt (fun s => q s i) (q' i) t := by
  exact ((EuclideanSpace.proj i : Plane →L[ℝ] ℝ).hasFDerivAt).comp_hasDerivAt t h

/-- The scalar energy model is derived from the literal gradient of the globally
defined Moreau potential and the actual vector differential equation. -/
def ValleyPath.ofVector (e : PowerExponent) {r ε : ℝ}
    (he : 0 < ε) (he1 : ε ≤ 1) (q u : ℝ → Plane)
    (hq : ContinuousOn q (Ici 0)) (hu : ContinuousOn u (Ici 0))
    (hqd : ∀ t > 0, HasDerivAt q (u t) t)
    (hud : ∀ t > 0,
      HasDerivAt u (-(r / t) • u t - gradient e ε (q t)) t)
    (hq0 : q 0 = point 2 1) (hu0 : u 0 = 0) : ValleyPath r e.p ε where
  x := fun t => q t 0
  y := fun t => q t 1
  v := fun t => u t 0
  w := fun t => u t 1
  F := fun t => potential e ε (q t)
  a := fun t => -gradient e ε (q t) 0
  b := fun t => gradient e ε (q t) 1
  cont_x := (EuclideanSpace.proj (0 : Fin 2) : Plane →L[ℝ] ℝ).continuous.comp_continuousOn hq
  cont_y := (EuclideanSpace.proj (1 : Fin 2) : Plane →L[ℝ] ℝ).continuous.comp_continuousOn hq
  cont_v := (EuclideanSpace.proj (0 : Fin 2) : Plane →L[ℝ] ℝ).continuous.comp_continuousOn hu
  cont_w := (EuclideanSpace.proj (1 : Fin 2) : Plane →L[ℝ] ℝ).continuous.comp_continuousOn hu
  cont_F := by
    have hcont : Continuous (potential e ε) :=
      continuous_iff_continuousAt.mpr (fun z => (potential_hasGradientAt e he z).continuousAt)
    exact hcont.comp_continuousOn hq
  deriv_x := fun t ht => hasDerivAt_coordinate (hqd t ht) 0
  deriv_y := fun t ht => hasDerivAt_coordinate (hqd t ht) 1
  deriv_v := by
    intro t ht
    convert hasDerivAt_coordinate (hud t ht) 0 using 1
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  deriv_w := by
    intro t ht
    convert hasDerivAt_coordinate (hud t ht) 1 using 1
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  deriv_F := by
    intro t ht
    convert (potential_hasGradientAt e he (q t)).hasFDerivAt.comp_hasDerivAt t
      (hqd t ht) using 1
    simp only [InnerProductSpace.toDual_apply, inner_eq]
    ring
  initial_x := by rw [hq0]; exact point_first 2 1
  initial_y := by rw [hq0]; exact point_second 2 1
  initial_v := by simp [hu0]
  initial_w := by simp [hu0]
  initial_F := by rw [hq0]; exact potential_initial_le_one e he
  nonneg_F := fun t _ => potential_nonneg e he (q t)
  nonneg_a := fun t _ => neg_nonneg.mpr (gradient_first_nonpos e ε (q t))
  upper_a := fun _ _ hx => gradient_drift_upper e he he1 hx
  upper_yb := fun _ _ hx => gradient_transverse_upper e he he1 hx
  lower_a := by
    intro M t hM _ hx hxM hF
    simpa only [div_mul_eq_mul_div] using gradient_drift_lower e he he1 hx hM hxM hF
  upper_y_sq := fun _ _ hM _ hx hxM hF => transverse_square_bound e he he1 hx hM hxM hF

/-- Every actual trajectory for this potential has a nondecreasing first coordinate.
In particular the excursion reached by a block is permanent. -/
theorem actual_first_coordinate_monotone (e : PowerExponent) {r ε : ℝ}
    (hr : 1 < r) (he : 0 < ε) (he1 : ε ≤ 1) (q u : ℝ → Plane)
    (hq : ContinuousOn q (Ici 0)) (hu : ContinuousOn u (Ici 0))
    (hqd : ∀ t > 0, HasDerivAt q (u t) t)
    (hud : ∀ t > 0,
      HasDerivAt u (-(r / t) • u t - gradient e ε (q t)) t)
    (hq0 : q 0 = point 2 1) (hu0 : u 0 = 0) :
    MonotoneOn (fun t => q t 0) (Ici 0) :=
  (ValleyPath.ofVector e he he1 q u hq hu hqd hud hq0 hu0).first_coordinate_monotone hr

#print axioms ValleyPath.ofVector
#print axioms actual_first_coordinate_monotone

end NesterovThreshold
