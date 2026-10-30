import PowerModel

set_option autoImplicit false
set_option maxHeartbeats 0

namespace NesterovThresholdModel

theorem potential_axis_zero (q : PowerExponent) {ε x : ℝ} (he : 0<ε) (hx : 0≤x) :
    potential q ε (point x 0)=0 := by
  apply le_antisymm _ (potential_nonneg q he _)
  have hg := gradient_first_nonpos q ε (point x 0)
  have hp := mul_nonpos_of_nonpos_of_nonneg hg hx
  rw [potential_formula,point_first,point_second,mul_zero,add_zero]
  nlinarith [mul_nonneg he.le (sq_nonneg (gradient q ε (point x 0) 0)),
    mul_nonneg he.le (sq_nonneg (gradient q ε (point x 0) 1))]

theorem potential_axis_minimizer (q : PowerExponent) {ε x : ℝ} (he : 0<ε) (hx : 0≤x)
    (z : Plane) : potential q ε (point x 0)≤potential q ε z := by
  rw [potential_axis_zero q he hx]
  exact potential_nonneg q he z

theorem arbitrarily_large_minimizers (q : PowerExponent) {ε : ℝ} (he : 0<ε) (M : ℝ) :
    ∃z:Plane, potential q ε z=0 ∧ M≤‖z‖ := by
  refine ⟨point (max M 0) 0,potential_axis_zero q he (le_max_right _ _),?_⟩
  have hx : 0≤max M 0 := le_max_right _ _
  have hn := norm_sq_eq (point (max M 0) 0)
  rw [point_first,point_second,zero_pow (by decide : 2≠0),add_zero] at hn
  have heq : ‖point (max M 0) 0‖=max M 0 := by nlinarith [norm_nonneg (point (max M 0) 0)]
  rw [heq]
  exact le_max_left _ _

#print axioms potential_axis_zero
#print axioms arbitrarily_large_minimizers

end NesterovThresholdModel
