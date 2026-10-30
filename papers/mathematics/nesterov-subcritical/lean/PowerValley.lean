import PowerExterior
import ScalarModelBounds

set_option autoImplicit false
set_option maxHeartbeats 0

namespace NesterovThresholdModel

/-- All finite-excursion estimates for the actual globally defined smooth potential. -/
theorem exterior_bounds (q : PowerExponent) {ε : ℝ} (he : 0<ε) (he1 : ε≤1)
    {z : Plane} (hz : 2≤z 0) :
    -gradient q ε z 0≤potential q ε z/z 0 ∧
    -gradient q ε z 0≤potential q ε z/2 ∧
    z 1*gradient q ε z 1≤q.p*potential q ε z+ε ∧
    ∀M:ℝ, 2≤M → z 0≤M → potential q ε z≤1 →
      (q.p-1)*(potential q ε z-ε)/(M+2)≤-gradient q ε z 0 ∧
      (z 1)^2≤4*(M+2)*potential q ε z+2*ε^2 := by
  obtain ⟨R,_hR,ha0,ha1,hb,hF,hV,hau,hal,hy,hs⟩ := exterior_representation q he hz
  exact scalar_exterior_estimates he he1 q.p_gt_one.le hz ha0 ha1 hb
    (by simpa only [mul_neg,sub_eq_add_neg,neg_sq] using hF)
    (by simpa only [mul_neg,sub_eq_add_neg] using hV)
    (by simpa only [mul_neg,sub_eq_add_neg] using hau)
    (by simpa only [mul_neg,sub_eq_add_neg] using hal)
    (by simpa only [mul_neg,sub_eq_add_neg] using hy)
    (by simpa only [mul_neg,sub_eq_add_neg] using hs)

theorem gradient_drift_upper (q : PowerExponent) {ε : ℝ} (he : 0<ε) (he1 : ε≤1)
    {z : Plane} (hz : 2≤z 0) :
    -gradient q ε z 0≤potential q ε z/2 := (exterior_bounds q he he1 hz).2.1

theorem gradient_transverse_upper (q : PowerExponent) {ε : ℝ} (he : 0<ε) (he1 : ε≤1)
    {z : Plane} (hz : 2≤z 0) :
    z 1*gradient q ε z 1≤q.p*potential q ε z+ε := (exterior_bounds q he he1 hz).2.2.1

theorem gradient_drift_lower (q : PowerExponent) {ε M : ℝ} (he : 0<ε) (he1 : ε≤1)
    {z : Plane} (hz : 2≤z 0) (hM : 2≤M) (hxM : z 0≤M) (hF : potential q ε z≤1) :
    (q.p-1)*(potential q ε z-ε)/(M+2)≤-gradient q ε z 0 :=
  ((exterior_bounds q he he1 hz).2.2.2 M hM hxM hF).1

theorem transverse_square_bound (q : PowerExponent) {ε M : ℝ} (he : 0<ε) (he1 : ε≤1)
    {z : Plane} (hz : 2≤z 0) (hM : 2≤M) (hxM : z 0≤M) (hF : potential q ε z≤1) :
    (z 1)^2≤4*(M+2)*potential q ε z+2*ε^2 :=
  ((exterior_bounds q he he1 hz).2.2.2 M hM hxM hF).2

#print axioms potential_convex
#print axioms potential_hasGradientAt
#print axioms gradient_lipschitz
#print axioms gradient_norm_le_three
#print axioms exterior_bounds

end NesterovThresholdModel
