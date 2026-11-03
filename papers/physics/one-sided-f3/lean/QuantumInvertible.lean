import QuantumTwoSided

/-!
# Invertible-filter value sets

Equation 10 uses invertible local filters.  These lemmas identify their exact
attainable-value set with the *open* Bloch ball, transport it through actual
whitening, and prove that success normalization does not alter the set.
Combined with the open-ball least-upper-bound theorem, this distinguishes
the supremum from its possible boundary-only attainment.
-/

set_option autoImplicit false

noncomputable section
open scoped BigOperators Matrix ComplexOrder
open Matrix

namespace FilteredF3

def quantumBobGLValues (M : Milne.CMatrix) : Set ℝ :=
  {v | ∃ F : Matrix Milne.Q Milne.Q ℂ,
    Matrix.trace (Milne.complexFiltered M F) = 1 ∧ F.det ≠ 0 ∧
    Milne.correlationSq (Milne.complexFiltered M F) = v}

def quantumNormalizedBobGLValues (M : Milne.CMatrix) : Set ℝ :=
  {v | ∃ F : Matrix Milne.Q Milne.Q ℂ, 0 < quantumSuccess M F ∧ F.det ≠ 0 ∧
    Milne.correlationSq (quantumNormalizedBob M F) = v}

/-- Every invertible local filter has strictly positive success probability
on every density matrix, even when that density matrix is singular. -/
theorem quantumSuccess_pos_of_invertible (M : Milne.CMatrix) (hM : Milne.Density M)
    (F : Matrix Milne.Q Milne.Q ℂ) (hdet : F.det ≠ 0) : 0 < quantumSuccess M F := by
  have hpsd := Milne.complexFiltered_psd hM.1 F
  have hnonneg : 0 ≤ quantumSuccess M F := Milne.psd_trace_nonneg hpsd
  by_contra hn
  have hp : quantumSuccess M F = 0 := le_antisymm (le_of_not_gt hn) hnonneg
  have ht : Matrix.trace (Milne.complexFiltered M F) = 0 := by
    rw [complex_filtered_trace_real M hM F, hp]
    rfl
  have hz := Milne.psd_eq_zero_of_trace_zero hpsd ht
  have hrec : Milne.complexFiltered (Milne.complexFiltered M F) F⁻¹ = M := by
    rw [complex_filtered_comp,
      Matrix.nonsing_inv_mul F (isUnit_iff_ne_zero.mpr hdet), complex_filtered_one]
  have hMzero : M = 0 := by
    rw [hz, Milne.complexFiltered] at hrec
    simpa using hrec.symm
  have htM := hM.2
  rw [hMzero] at htM
  simpa using htM

/-- The success condition in the operational definition excludes no
invertible filter. -/
theorem quantumNormalizedBobGLValues_unrestricted (M : Milne.CMatrix)
    (hM : Milne.Density M) :
    quantumNormalizedBobGLValues M =
      {v | ∃ F : Matrix Milne.Q Milne.Q ℂ, F.det ≠ 0 ∧
        Milne.correlationSq (quantumNormalizedBob M F) = v} := by
  ext v
  constructor
  · rintro ⟨F, hp, hd, hv⟩
    exact ⟨F, hd, hv⟩
  · rintro ⟨F, hd, hv⟩
    exact ⟨F, quantumSuccess_pos_of_invertible M hM F hd, hd, hv⟩

/-- Invertibility of an arbitrary complex effect is exactly strict Bloch-ball
membership.  The complex polar unitary is not restricted. -/
theorem complex_filter_invertible_iff_open_ball (F : Matrix Milne.Q Milne.Q ℂ)
    (x : Milne.V3) (hx : Milne.vSq x ≤ 1) (hF : Fᴴ*F = 1+Milne.spin x) :
    F.det ≠ 0 ↔ Milne.vSq x < 1 := by
  have he : star F.det * F.det = ((1-Milne.vSq x : ℝ) : ℂ) := by
    rw [← Matrix.det_conjTranspose, ← Matrix.det_mul, hF, Milne.qubitBall_det]
  constructor
  · intro hn
    have hne : Milne.vSq x ≠ 1 := by
      intro hz
      rw [hz] at he
      norm_num at he
      exact hn he
    exact lt_of_le_of_ne hx hne
  · intro hi hz
    rw [hz] at he
    have hc : (1-Milne.vSq x : ℝ) = 0 := by
      have h := congrArg Complex.re he
      simpa using h.symm
    linarith

theorem canonical_quantum_GL_attainable_values (c : Milne.V3) (S : Milne.T3)
    (hM : (Milne.blochState c 0 S).PosSemidef) :
    quantumBobGLValues (Milne.blochState c 0 S) =
      {v : ℝ | ∃ x : Fin 3 → ℝ, radiusSq x < 1 ∧
        matrixObjective (Milne.tSq S) (-Milne.orbitK c S) (Milne.ttVec S c) x = v} := by
  ext v
  constructor
  · rintro ⟨F, hTr, hdet, hv⟩
    have hFTr := (canonical_filter_trace_iff _ (Milne.blochState_canonical c S) F).mp hTr
    obtain ⟨x, hx, hF⟩ := Milne.complex_filter_effect_coordinates F hFTr
    refine ⟨x, (complex_filter_invertible_iff_open_ball F x hx hF).mp hdet, ?_⟩
    rw [← bloch_orbit_matrix_objective,
      ← Milne.canonical_complex_filter_correlation c x S hM F hF]
    exact hv
  · rintro ⟨x, hx, hv⟩
    have h := Milne.canonical_filter_realizes_ball c x S hM (le_of_lt hx)
    refine ⟨Milne.qubitBallFilter x (le_of_lt hx), h.2.1.2,
      Milne.qubitBallFilter_det_ne_zero x hx, ?_⟩
    rw [h.2.2, bloch_orbit_matrix_objective]
    exact hv

theorem quantum_GL_values_whitening (M : Milne.CMatrix) (hM : Milne.Density M)
    (hdet : (Milne.partialB M).det ≠ 0) :
    quantumBobGLValues M = quantumBobGLValues (Milne.canonicalize M hM) := by
  have hB : (Milne.bobFilter M hM).det ≠ 0 :=
    isUnit_iff_ne_zero.mp (Milne.bobFilter_isUnit M hM hdet)
  have hBi : ((Milne.bobFilter M hM)⁻¹).det ≠ 0 :=
    isUnit_iff_ne_zero.mp (Matrix.isUnit_nonsing_inv_det _ (Milne.bobFilter_isUnit M hM hdet))
  ext v
  constructor
  · rintro ⟨F, hTr, hd, hv⟩
    refine ⟨F*Milne.bobFilter M hM, ?_, ?_, ?_⟩
    · rw [← complex_filtered_comp, canonicalize_complex_reconstruction M hM hdet]
      exact hTr
    · rw [Matrix.det_mul]
      exact mul_ne_zero hd hB
    · rw [← complex_filtered_comp, canonicalize_complex_reconstruction M hM hdet]
      exact hv
  · rintro ⟨F, hTr, hd, hv⟩
    refine ⟨F*(Milne.bobFilter M hM)⁻¹, ?_, ?_, ?_⟩
    · rw [← complex_filtered_comp, ← canonicalize_complex_filtered M hM]
      exact hTr
    · rw [Matrix.det_mul]
      exact mul_ne_zero hd hBi
    · rw [← complex_filtered_comp, ← canonicalize_complex_filtered M hM]
      exact hv

theorem singular_Bob_quantum_GL_values (M : Milne.CMatrix) (hM : Milne.Density M)
    (hdet : (Milne.partialB M).det = 0) :
    quantumBobGLValues M = {Milne.blochSq (Milne.partialA M)} := by
  ext v
  constructor
  · rintro ⟨F, hTr, hd, hv⟩
    exact hv.symm.trans (singular_Bob_filter_value M hM hdet F hTr)
  · intro hv
    change v = Milne.blochSq (Milne.partialA M) at hv
    refine ⟨1, ?_, by simp, ?_⟩
    · rw [complex_filtered_one]
      exact hM.2
    · rw [complex_filtered_one, hv]
      exact Milne.singular_Bob_correlationSq_eq_blochSq M hM hdet

theorem quantum_normalization_GL_value_sets (M : Milne.CMatrix) (hM : Milne.Density M) :
    quantumNormalizedBobGLValues M = quantumBobGLValues M := by
  ext v
  constructor
  · rintro ⟨F, hp, hd, hv⟩
    refine ⟨(((Real.sqrt (quantumSuccess M F))⁻¹ : ℝ) : ℂ) • F, ?_, ?_, ?_⟩
    · rw [quantumNormalizedBob_realized M F hp]
      exact quantumNormalizedBob_trace M hM F hp
    · rw [Matrix.det_smul]
      apply mul_ne_zero _ hd
      apply pow_ne_zero
      have hs : Real.sqrt (quantumSuccess M F) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hp)
      exact_mod_cast inv_ne_zero hs
    · rw [quantumNormalizedBob_realized M F hp]
      exact hv
  · rintro ⟨F, hTr, hd, hv⟩
    have hp : quantumSuccess M F = 1 := by simp [quantumSuccess, hTr]
    refine ⟨F, by rw [hp]; norm_num, hd, ?_⟩
    simpa [quantumNormalizedBob, hp] using hv

def quantumNormalizedAliceGLValues (M : Milne.CMatrix) : Set ℝ :=
  {v | ∃ F : Matrix Milne.Q Milne.Q ℂ, 0 < quantumAliceSuccess M F ∧ F.det ≠ 0 ∧
    Milne.correlationSq (quantumNormalizedAlice M F) = v}

theorem quantumNormalizedAlice_GL_values_swap (M : Milne.CMatrix) :
    quantumNormalizedAliceGLValues M = quantumNormalizedBobGLValues (quantumSwap M) := by
  ext v
  simp only [quantumNormalizedAliceGLValues, quantumNormalizedBobGLValues, Set.mem_setOf_eq,
    ← quantumNormalizedAlice_swap, quantumSwap_correlationSq, quantumAlice_success_swap]

end FilteredF3
