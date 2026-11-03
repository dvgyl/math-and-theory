import MilneGeometryBridge
import MilneGeometrySharpness
import MilneGeometryConsequences

/-! The exact skew envelope stated directly for arbitrary density matrices
and their actual local Pauli expectations, with its exact feasibility range. -/

open scoped BigOperators Matrix ComplexOrder
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
noncomputable section
namespace Milne

theorem geometryLocalA_blochState (a b : V3) (T : T3) :
    geometryLocalA (blochState a b T) = a := by
  funext i
  fin_cases i <;>
    simp [geometryLocalA, blochState, onAlice, onBob, pauli, pauliZ,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fin.sum_univ_three, Complex.mul_re, Complex.mul_im]
  all_goals ring

theorem geometryLocalB_blochState (a b : V3) (T : T3) :
    geometryLocalB (blochState a b T) = b := by
  funext i
  fin_cases i <;>
    simp [geometryLocalB, blochState, onAlice, onBob, pauli, pauliZ,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fin.sum_univ_three, Complex.mul_re, Complex.mul_im]
  all_goals ring

/-- All physical values at prescribed canonical centre and radial support. -/
def geometryPhysicalSkewSpectrum (c t : ℝ) : Set ℝ :=
  {x | ∃ M : CMatrix, Density M ∧ geometryLocalA M = c • geometryEz ∧
    geometryLocalB M = 0 ∧ vSq (ttVec (correlation M) geometryEz) = t^2 ∧
    correlationSq M = x}

theorem geometryPhysicalSkewSpectrum_eq (c t : ℝ) :
    geometryPhysicalSkewSpectrum c t = geometrySkewSpectrum c t := by
  ext x
  constructor
  · rintro ⟨M,hM,ha,hb,hq,hx⟩
    refine ⟨correlation M, ?_, hq, hx⟩
    have hr := geometry_density_reconstruction M hM
    rw [ha, hb] at hr
    rw [hr]
    exact hM.1
  · rintro ⟨T,hM,hq,hx⟩
    refine ⟨blochState (c • geometryEz) 0 T, blochState_density _ _ _ hM,
      geometryLocalA_blochState _ _ _, geometryLocalB_blochState _ _ _, ?_, ?_⟩
    · simpa only [blochState_correlations] using hq
    · simpa only [blochState_correlationSq] using hx

/-- The exact centre/skew maximum for arbitrary physical density matrices. -/
theorem geometryPhysicalSkewEnvelope_isGreatest {c t : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1-c) :
    IsGreatest (geometryPhysicalSkewSpectrum c t) (1-c^2+2*t^2) := by
  rw [geometryPhysicalSkewSpectrum_eq]
  exact geometrySkewEnvelope_isGreatest hc0 hc1 ht0 ht1

/-- The proposed parameter range is exactly feasible, not just sufficient. -/
theorem geometryPhysicalSkewSpectrum_nonempty_iff {c t : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (ht0 : 0 ≤ t) :
    (geometryPhysicalSkewSpectrum c t).Nonempty ↔ t ≤ 1-c := by
  rw [geometryPhysicalSkewSpectrum_eq]
  constructor
  · rintro ⟨x,T,hM,hq,hx⟩
    have h := canonical_radial_feasibility c geometryEz T geometryEz_unit hM
    rw [hq] at h
    nlinarith
  · intro ht1
    exact ⟨1-c^2+2*t^2, (geometrySkewEnvelope_isGreatest hc0 hc1 ht0 ht1).1⟩

#print axioms geometryPhysicalSkewEnvelope_isGreatest
#print axioms geometryPhysicalSkewSpectrum_nonempty_iff

end Milne
