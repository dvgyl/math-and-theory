import MilneJointPhysicalStability
import MilneJointSpectrum

open scoped BigOperators Matrix ComplexOrder
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 8000000

noncomputable section
namespace Milne

/-- An independent restatement directly about an arbitrary actual density
matrix, without supplying Bloch directions or a centre identity as premises.
The existential reference is certified to be positive and trace one. -/
theorem arbitrary_joint_trace_rigidity (M : CMatrix) (hM : Density M)
    (hr : blochLength (partialB M) < 1) :
    let c := steeringCenter M hM
    let r := blochLength (partialB M)
    ∃ n m : V3, vSq n = 1 ∧ vSq m = 1 ∧
      geometryLocalB M = r • m ∧
      geometryLocalA (canonicalize M hM) = c • n ∧
      ∃ hR : Density (jointLowerRotated c r n m),
        (hermitianTraceNorm (hM.1.1.sub hR.1.1))^2 ≤
          (1+r^2)*(correlationSq M-(jointLowerX c r)^2) := by
  dsimp only
  let c := steeringCenter M hM
  let r := blochLength (partialB M)
  have hd := bob_det_ne_zero_of_blochLength_lt_one M hM hr
  have hN := canonicalize_density M hM hd
  obtain ⟨n,hn,hcn⟩ := joint_exists_unit_direction (geometryLocalA (canonicalize M hM))
  obtain ⟨m,hm,hbm⟩ := joint_exists_unit_direction (geometryLocalB M)
  have hc : c = Real.sqrt (vSq (geometryLocalA (canonicalize M hM))) := by
    dsimp only [c]
    rw [steeringCenter_of_nonsingular M hM hd]
    rw [center,center_actual_partialA (canonicalize M hM) hN,qubitState_blochSq]
  have hb : r = Real.sqrt (vSq (geometryLocalB M)) := by
    dsimp only [r]
    rw [blochLength,center_actual_partialB M hM,qubitState_blochSq]
  rw [← hc] at hcn
  rw [← hb] at hbm
  have hrec : blochState (geometryLocalA M) (r • m) (correlation M) = M := by
    rw [← hbm,geometry_density_reconstruction M hM]
  have hphysical : Density (blochState (geometryLocalA M) (r • m) (correlation M)) := by
    rw [hrec]
    exact hM
  have hcentre : geometryLocalA M-tVec (correlation M) (r • m) =
      ((1-r^2)*c) • n := by
    rw [← hbm,canonicalize_center_numerator M hM hd,hcn,hbm,
      vSq_smul,hm,mul_one,smul_smul]
  have h := joint_physical_trace_rigidity (geometryLocalA M) n m (correlation M) c r
    hphysical (steeringCenter_nonneg M hM) (steeringCenter_le_one M hM)
    (blochLength_nonneg (partialB M)) hr hn hm hcentre
  refine ⟨n,m,hn,hm,hbm,hcn,h.1,?_⟩
  simpa only [hrec,jointLowerRotated] using h.2

/-- Independent unpacking of the full range into existence of actual matrices.
Neither endpoint is a scalar surrogate, and all intermediate values occur. -/
theorem actual_joint_value_iff (c r y : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∃ (M : CMatrix) (hM : Density M), steeringCenter M hM = c ∧
      blochLength (partialB M) = r ∧ correlationSq M = y) ↔
      (jointLowerX c r)^2 ≤ y ∧ y ≤ steeringQuadratic c r := by
  change y ∈ jointSteeringSpectrum c r ↔ y ∈ Set.Icc _ _
  rw [jointSteeringSpectrum_eq_Icc hc0 hc1 hr0 hr1]

end Milne

#print axioms Milne.arbitrary_joint_trace_rigidity
#print axioms Milne.actual_joint_value_iff
