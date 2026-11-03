import QuantumExtremizers
import OpenBallSupremum

/-!
# Exact values for Equation 10's invertible-filter suprema

This is the end-to-end theorem chain: arbitrary actual complex density
matrix → successful invertible local filters → exact whitening → open
physical effect ball → unconditional spectral algebraic formula.  The
singular-marginal branch is proved separately as an exact singleton.
-/

set_option autoImplicit false

noncomputable section
open scoped BigOperators Matrix ComplexOrder
open Matrix

namespace FilteredF3

theorem closed_form_canonical_quantum_GL (c : Milne.V3) (S : Milne.T3)
    (hM : (Milne.blochState c 0 S).PosSemidef) :
    IsLUB (quantumBobGLValues (Milne.blochState c 0 S)) (quantumCanonicalValue c S) := by
  rw [canonical_quantum_GL_attainable_values c S hM]
  exact open_ball_real_matrix_three (Milne.tSq S) (-Milne.orbitK c S)
    (Milne.orbitK_hermitian c S).neg (Milne.ttVec S c)

theorem closed_form_arbitrary_quantum_Bob_GL (M : Milne.CMatrix) (hM : Milne.Density M)
    (hdet : (Milne.partialB M).det ≠ 0) :
    IsLUB (quantumBobGLValues M) (quantumBobAlgebraicValue M hM) := by
  rw [quantum_GL_values_whitening M hM hdet]
  have hrecon := canonicalize_bloch_reconstruction M hM hdet
  have hPSD : (Milne.blochState (Milne.geometryLocalA (Milne.canonicalize M hM)) 0
      (Milne.correlation (Milne.canonicalize M hM))).PosSemidef := by
    rw [hrecon]
    exact Milne.canonicalize_psd M hM
  have h := closed_form_canonical_quantum_GL _ _ hPSD
  rw [hrecon] at h
  exact h

/-- The squared F3 supremum over invertible filters for every two-qubit
state, with no rank or genericity assumptions. -/
theorem closed_form_all_quantum_Bob_GL (M : Milne.CMatrix) (hM : Milne.Density M) :
    IsLUB (quantumBobGLValues M) (quantumBobExactValue M hM) := by
  by_cases hd : (Milne.partialB M).det = 0
  · rw [quantumBobExactValue, if_pos hd, singular_Bob_quantum_GL_values M hM hd]
    exact ⟨fun v hv => le_of_eq hv, fun u hu => hu rfl⟩
  · rw [quantumBobExactValue, if_neg hd]
    exact closed_form_arbitrary_quantum_Bob_GL M hM hd

theorem closed_form_success_normalized_Bob_GL (M : Milne.CMatrix) (hM : Milne.Density M) :
    IsLUB (quantumNormalizedBobGLValues M) (quantumBobExactValue M hM) := by
  rw [quantum_normalization_GL_value_sets M hM]
  exact closed_form_all_quantum_Bob_GL M hM

/-- Both squared one-sided quantities in the actual invertible-filter class. -/
theorem closed_form_both_invertible_normalized (M : Milne.CMatrix) (hM : Milne.Density M) :
    IsLUB (quantumNormalizedAliceGLValues M) (quantumAliceExactValue M hM) ∧
    IsLUB (quantumNormalizedBobGLValues M) (quantumBobExactValue M hM) := by
  constructor
  · rw [quantumNormalizedAlice_GL_values_swap]
    exact closed_form_success_normalized_Bob_GL (quantumSwap M) (quantumSwap_density M hM)
  · exact closed_form_success_normalized_Bob_GL M hM

theorem quantumNormalizedBobGLValues_nonempty (M : Milne.CMatrix) (hM : Milne.Density M) :
    (quantumNormalizedBobGLValues M).Nonempty := by
  rw [quantum_normalization_GL_value_sets M hM]
  refine ⟨Milne.correlationSq M, 1, ?_, by simp, ?_⟩
  · rw [complex_filtered_one]
    exact hM.2
  · rw [complex_filtered_one]

theorem sqrt_image_isLUB {S : Set ℝ} {V : ℝ} (hne : S.Nonempty) (hV : IsLUB S V) :
    IsLUB (Real.sqrt '' S) (Real.sqrt V) := by
  constructor
  · rintro v ⟨a, ha, rfl⟩
    exact Real.sqrt_le_sqrt (hV.1 ha)
  · intro u hu
    obtain ⟨a, ha⟩ := hne
    have hu0 : 0 ≤ u := le_trans (Real.sqrt_nonneg a) (hu ⟨a, ha, rfl⟩)
    apply Real.sqrt_le_iff.mpr
    refine ⟨hu0, hV.2 ?_⟩
    intro v hv
    exact (Real.sqrt_le_iff.mp (hu ⟨v, hv, rfl⟩)).2

/-- The F3 values themselves, rather than their squares. -/
def quantumF3BobGLValues (M : Milne.CMatrix) : Set ℝ :=
  Real.sqrt '' quantumNormalizedBobGLValues M

def quantumF3AliceGLValues (M : Milne.CMatrix) : Set ℝ :=
  Real.sqrt '' quantumNormalizedAliceGLValues M

/-- End-to-end exact closed forms for both one-sided F3 suprema.  The result
is a least upper bound, so it correctly covers boundary-only extrema that
cannot be attained by an invertible local filter. -/
theorem equation10_both_closed_forms (M : Milne.CMatrix) (hM : Milne.Density M) :
    IsLUB (quantumF3AliceGLValues M) (Real.sqrt (quantumAliceExactValue M hM)) ∧
    IsLUB (quantumF3BobGLValues M) (Real.sqrt (quantumBobExactValue M hM)) := by
  have hboth := closed_form_both_invertible_normalized M hM
  constructor
  · apply sqrt_image_isLUB _ hboth.1
    rw [quantumNormalizedAlice_GL_values_swap]
    exact quantumNormalizedBobGLValues_nonempty (quantumSwap M) (quantumSwap_density M hM)
  · exact sqrt_image_isLUB (quantumNormalizedBobGLValues_nonempty M hM) hboth.2

end FilteredF3
