import MilneSteering
import MilneSingular

open scoped BigOperators Matrix ComplexOrder
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

noncomputable section

namespace Milne

theorem singular_Bob_correlationSq_eq_blochSq (M : CMatrix) (hM : Density M)
    (hd : (partialB M).det = 0) : correlationSq M = blochSq (partialA M) := by
  have h := correlationSq_purityDifference M hM
  rw [singular_Bob_purityDifference_zero M hM hd, singular_Bob_blochSq M hM hd] at h
  simpa using h

theorem singular_Bob_correlationSq_le_one (M : CMatrix) (hM : Density M)
    (hd : (partialB M).det = 0) : correlationSq M ≤ 1 := by
  rw [singular_Bob_correlationSq_eq_blochSq M hM hd]
  have h := blochSq_psd_le (partialA_psd hM.1)
  rw [trace_partialA,hM.2] at h
  simpa using h

/-- The length of Alice's steering-ellipsoid center, including the point
ellipsoid when Bob's marginal is pure. For a nonsingular marginal this is
computed by the positive canonicalizing filter. -/
def steeringCenter (M : CMatrix) (hM : Density M) : ℝ :=
  if (partialB M).det = 0 then center M else center (canonicalize M hM)

theorem steeringCenter_nonneg (M : CMatrix) (hM : Density M) :
    0 ≤ steeringCenter M hM := by
  unfold steeringCenter
  split_ifs <;> exact center_nonneg _

theorem steeringCenter_le_one (M : CMatrix) (hM : Density M) :
    steeringCenter M hM ≤ 1 := by
  unfold steeringCenter
  split_ifs with hd
  · exact center_le_one M hM
  · exact center_le_one _ (canonicalize_density M hM hd)

theorem steeringCenter_of_nonsingular (M : CMatrix) (hM : Density M)
    (hd : (partialB M).det ≠ 0) :
    steeringCenter M hM = center (canonicalize M hM) := by
  simp only [steeringCenter, if_neg hd]

/-- The universal sharp squared three-setting steering envelope for every
complex two-qubit density matrix, with no rank assumption. -/
theorem all_states_steering_bound (M : CMatrix) (hM : Density M) :
    correlationSq M ≤ steeringEnvelopeSq (steeringCenter M hM) := by
  by_cases hd : (partialB M).det = 0
  · exact (singular_Bob_correlationSq_le_one M hM hd).trans
      (steeringEnvelopeSq_ge_one (steeringCenter_nonneg M hM))
  · rw [steeringCenter_of_nonsingular M hM hd]
    exact arbitrary_steering_bound M hM hd

/-- Normalization agrees with the optimized three-setting linear steering
quantity F3: its local-hidden-state threshold is one. -/
def steeringValue (M : CMatrix) : ℝ := Real.sqrt (correlationSq M)

theorem all_states_steering_value_bound (M : CMatrix) (hM : Density M) :
    steeringValue M ≤ Real.sqrt (steeringEnvelopeSq (steeringCenter M hM)) :=
  Real.sqrt_le_sqrt (all_states_steering_bound M hM)

theorem no_three_setting_violation (M : CMatrix) (hM : Density M)
    (hc : 2/3 ≤ steeringCenter M hM) : steeringValue M ≤ 1 := by
  have h := all_states_steering_value_bound M hM
  rwa [steeringEnvelopeSq_eq_one hc, Real.sqrt_one] at h

theorem violation_requires_center_lt_two_thirds (M : CMatrix) (hM : Density M)
    (hv : 1 < steeringValue M) : steeringCenter M hM < 2/3 := by
  by_contra hn
  exact (not_lt_of_ge (no_three_setting_violation M hM (le_of_not_gt hn))) hv

/-- The fully entangled-fraction inequality for every state and
every maximally entangled unit vector, including singular Bob marginals. -/
theorem all_states_entangled_overlap_bound (M : CMatrix) (hM : Density M)
    (v : QQ → ℂ) (hv : MaximallyEntangled v) :
    overlap M v ≤ 1 - steeringCenter M hM / 2 := by
  by_cases hd : (partialB M).det = 0
  · have h := singular_Bob_entangled_overlap_bound M hM hd v hv
    have hc := steeringCenter_le_one M hM
    linarith
  · rw [steeringCenter_of_nonsingular M hM hd]
    exact arbitrary_entangled_overlap_bound M hM hd v hv

end Milne
