import QuantumBloch

/-!
# The pure filtered-marginal branch

This module proves the missing endpoint at the level of actual complex
matrices: a two-qubit density matrix with singular Bob marginal is a tensor
product, and every successful Bob filter has the same squared correlation
norm.  No continuity argument or inverse of a singular marginal is used.
-/

set_option autoImplicit false

noncomputable section
open scoped BigOperators Matrix ComplexOrder
open Matrix
set_option maxHeartbeats 4000000

namespace FilteredF3

def quantumTensor (A B : Matrix Milne.Q Milne.Q ℂ) : Milne.CMatrix :=
  fun i j => A i.1 j.1 * B i.2 j.2

theorem rank_one_qubit_sandwich (B X : Matrix Milne.Q Milne.Q ℂ)
    (hdet : B.det = 0) : B*X*B = Matrix.trace (B*X) • B := by
  have hid : B*X*B = Matrix.trace (B*X) • B -
      B.det • !![X 1 1, -X 0 1; -X 1 0, X 0 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.trace, Matrix.diag, Fin.sum_univ_two,
        Matrix.det_fin_two] <;> ring
  simpa [hdet] using hid

theorem supported_qubit_rank_one (B X : Matrix Milne.Q Milne.Q ℂ)
    (hdet : B.det = 0) (hTr : Matrix.trace B = 1) (hs : X = B*X*B) :
    X = Matrix.trace X • B := by
  have he : X = Matrix.trace (B*X) • B := hs.trans (rank_one_qubit_sandwich B X hdet)
  have ht : Matrix.trace X = Matrix.trace (B*X) := by
    simpa [Matrix.trace_smul, hTr] using congrArg Matrix.trace he
  rwa [ht]

/-- Actual tensor-product factorization forced by positivity and a pure
filtered marginal. -/
theorem density_singular_Bob_product (M : Milne.CMatrix) (hM : Milne.Density M)
    (hdet : (Milne.partialB M).det = 0) :
    M = quantumTensor (Milne.partialA M) (Milne.partialB M) := by
  have hs := Milne.singular_Bob_support M hM hdet
  have ht : Matrix.trace (Milne.partialB M) = 1 := by
    rw [Milne.trace_partialB, hM.2]
  have hb (a c : Milne.Q) : Milne.bobBlock M a c =
      Matrix.trace (Milne.bobBlock M a c) • Milne.partialB M := by
    apply supported_qubit_rank_one _ _ hdet ht
    have h := congrArg (fun N => Milne.bobBlock N a c) hs
    dsimp only at h
    rwa [Milne.bobBlock_filter] at h
  ext i j
  have h := congrArg (fun X : Matrix Milne.Q Milne.Q ℂ => X i.2 j.2) (hb i.1 j.1)
  simpa [quantumTensor, Milne.bobBlock, Matrix.trace, Matrix.diag, Milne.partialA]
    using h

theorem quantumTensor_partialA (A B : Matrix Milne.Q Milne.Q ℂ) :
    Milne.partialA (quantumTensor A B) = Matrix.trace B • A := by
  ext i j
  simp [quantumTensor, Milne.partialA, Matrix.trace, Matrix.diag, Finset.mul_sum,
    mul_comm]
  ring

theorem quantumTensor_partialB (A B : Matrix Milne.Q Milne.Q ℂ) :
    Milne.partialB (quantumTensor A B) = Matrix.trace A • B := by
  ext i j
  simp [quantumTensor, Milne.partialB, Matrix.trace, Matrix.diag, Finset.sum_mul]
  ring

theorem quantumTensor_trace (A B : Matrix Milne.Q Milne.Q ℂ) :
    Matrix.trace (quantumTensor A B) = Matrix.trace A * Matrix.trace B := by
  rw [← Milne.trace_partialB, quantumTensor_partialB, Matrix.trace_smul, smul_eq_mul]

theorem quantumTensor_filtered (A B F : Matrix Milne.Q Milne.Q ℂ) :
    Milne.complexFiltered (quantumTensor A B) F = quantumTensor A (F*B*Fᴴ) := by
  ext i j
  rcases i with ⟨a,b⟩
  rcases j with ⟨c,d⟩
  fin_cases a <;> fin_cases c <;>
    simp [Milne.complexFiltered, Milne.onBob, quantumTensor, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two] <;> ring

/-- All normalized complex filters on a pure marginal preserve the squared
F3 value exactly.  Filters with zero success probability do not satisfy the
trace-one hypothesis. -/
theorem singular_Bob_filter_value (M : Milne.CMatrix) (hM : Milne.Density M)
    (hdet : (Milne.partialB M).det = 0) (F : Matrix Milne.Q Milne.Q ℂ)
    (hTr : Matrix.trace (Milne.complexFiltered M F) = 1) :
    Milne.correlationSq (Milne.complexFiltered M F) = Milne.blochSq (Milne.partialA M) := by
  have hp := density_singular_Bob_product M hM hdet
  have hA : Matrix.trace (Milne.partialA M) = 1 := by
    rw [Milne.trace_partialA, hM.2]
  have hC : Matrix.trace (F*Milne.partialB M*Fᴴ) = 1 := by
    conv_lhs at hTr => rw [hp]
    rwa [quantumTensor_filtered, quantumTensor_trace, hA, one_mul] at hTr
  have hpa : Milne.partialA (Milne.complexFiltered M F) = Milne.partialA M := by
    conv_lhs => rw [hp]
    rw [quantumTensor_filtered, quantumTensor_partialA, hC, one_smul]
  have hpb : Milne.partialB (Milne.complexFiltered M F) = F*Milne.partialB M*Fᴴ := by
    conv_lhs => rw [hp]
    rw [quantumTensor_filtered, quantumTensor_partialB, hA, one_smul]
  have hd : (Milne.partialB (Milne.complexFiltered M F)).det = 0 := by
    rw [hpb, Matrix.det_mul, Matrix.det_mul, hdet]
    ring
  rw [Milne.singular_Bob_correlationSq_eq_blochSq _
    ⟨Milne.complexFiltered_psd hM.1 F, hTr⟩ hd, hpa]

theorem complex_filtered_one (M : Milne.CMatrix) :
    Milne.complexFiltered M (1 : Matrix Milne.Q Milne.Q ℂ) = M := by
  simp [Milne.complexFiltered, Milne.onBob_one]

/-- The complete attainable-value set in the singular-marginal branch is a
singleton.  This is stronger than an upper-bound or limiting statement. -/
theorem singular_Bob_quantum_values (M : Milne.CMatrix) (hM : Milne.Density M)
    (hdet : (Milne.partialB M).det = 0) :
    quantumBobValues M = {Milne.blochSq (Milne.partialA M)} := by
  ext v
  constructor
  · rintro ⟨F, hTr, hv⟩
    exact hv.symm.trans (singular_Bob_filter_value M hM hdet F hTr)
  · intro hv
    change v = Milne.blochSq (Milne.partialA M) at hv
    refine ⟨1, ?_, ?_⟩
    · rw [complex_filtered_one]
      exact hM.2
    · rw [complex_filtered_one, hv]
      exact Milne.singular_Bob_correlationSq_eq_blochSq M hM hdet

def quantumBobExactValue (M : Milne.CMatrix) (hM : Milne.Density M) : ℝ :=
  if (Milne.partialB M).det = 0 then Milne.blochSq (Milne.partialA M)
  else quantumBobAlgebraicValue M hM

/-- Every two-qubit density matrix, including the pure-marginal branch.
All remaining filter optimization has been eliminated from the result. -/
theorem closed_form_all_quantum_Bob (M : Milne.CMatrix) (hM : Milne.Density M) :
    IsGreatest (quantumBobValues M) (quantumBobExactValue M hM) := by
  by_cases hd : (Milne.partialB M).det = 0
  · rw [quantumBobExactValue, if_pos hd, singular_Bob_quantum_values M hM hd]
    exact ⟨rfl, fun v hv => le_of_eq hv⟩
  · rw [quantumBobExactValue, if_neg hd]
    exact closed_form_arbitrary_quantum_Bob M hM hd

theorem quantumBobExactValue_nonneg (M : Milne.CMatrix) (hM : Milne.Density M) :
    0 ≤ quantumBobExactValue M hM := by
  obtain ⟨F, hTr, hv⟩ := (closed_form_all_quantum_Bob M hM).1
  rw [← hv]
  exact Milne.correlationSq_nonneg _

end FilteredF3
