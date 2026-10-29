module
public import MilneAllStates

@[expose] public section

open scoped BigOperators Matrix ComplexOrder
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

noncomputable section

namespace Milne

theorem steeringQuadratic_lt_one {c r : ℝ} (hc : 2/3 ≤ c) (hc1 : c ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r < 1) : steeringQuadratic c r < 1 := by
  have hA : 0 < 4*c-2-c^2 := by
    have hp := mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr hc1)
    nlinarith
  have hB : 0 ≤ 6*c-4 := by linarith
  have hpos := mul_pos (sq_pos_of_pos (sub_pos.mpr hr1)) hA
  have hnonneg := mul_nonneg (mul_nonneg hr0 (le_of_lt (sub_pos.mpr hr1))) hB
  have hid : 1-steeringQuadratic c r =
      (1-r)^2*(4*c-2-c^2)+r*(1-r)*(6*c-4) := by
    unfold steeringQuadratic
    ring
  linarith

theorem fullrank_Bob_blochLength_lt_one (M : CMatrix) (hM : Density M)
    (hd : (partialB M).det ≠ 0) : blochLength (partialB M) < 1 := by
  have hB := partialB_psd hM.1
  have hd0 := psd_det_nonneg hB
  have hdpos : 0 < (partialB M).det.re := by
    apply lt_of_le_of_ne hd0
    intro hz
    apply hd
    apply Complex.ext
    · simpa using hz.symm
    · simpa using hermitian_det_im hB.1
  have hbloch := blochSq_det_identity hB.1
  rw [trace_partialB,hM.2] at hbloch
  norm_num at hbloch
  have hs := blochLength_sq (partialB M)
  have hn := blochLength_nonneg (partialB M)
  nlinarith

/-- The flat branch is not attained at any fixed center below one.
This includes the threshold c=2/3 and both marginal-rank cases. -/
theorem no_maximizer_on_flat_branch (M : CMatrix) (hM : Density M)
    (hc : 2/3 ≤ steeringCenter M hM) (hc1 : steeringCenter M hM < 1) :
    correlationSq M < 1 := by
  by_cases hd : (partialB M).det = 0
  · have hEq := singular_Bob_correlationSq_eq_blochSq M hM hd
    have hcenter : steeringCenter M hM = center M := by
      simp only [steeringCenter,if_pos hd]
    rw [hcenter] at hc1
    have hs : center M^2 = blochSq (partialA M) := Real.sq_sqrt (blochSq_nonneg _)
    have hn := center_nonneg M
    rw [hEq]
    nlinarith
  · have hq := filtered_steering_quadratic_bound (canonicalize M hM)
      (canonicalize_density M hM hd) (canonicalize_partialB M hM hd)
      (bobFilter M hM) (bobFilter_hermitian M hM) (bobFilter_trace M hM)
    dsimp only at hq
    rw [canonicalize_reconstruction M hM hd] at hq
    rw [steeringCenter_of_nonsingular M hM hd] at hc hc1
    exact hq.trans_lt (steeringQuadratic_lt_one hc (le_of_lt hc1)
      (blochLength_nonneg _) (fullrank_Bob_blochLength_lt_one M hM hd))

end Milne
