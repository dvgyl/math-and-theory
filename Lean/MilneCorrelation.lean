module
public import MilneBlochDefs
public import MilneQubit
public import MilnePurityCovariance

@[expose] public section

open scoped BigOperators Matrix ComplexOrder
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

noncomputable section

namespace Milne

def pauliPair (i j : Fin 3) : CMatrix :=
  fun p q => pauli i p.1 q.1 * pauli j p.2 q.2

def correlation (M : CMatrix) (i j : Fin 3) : ℝ :=
  (Matrix.trace (M * pauliPair i j)).re

/-- The squared Frobenius norm of the physical Pauli correlation matrix,
equivalently the squared optimized three-setting linear steering value. -/
def correlationSq (M : CMatrix) : ℝ := ∑ i, ∑ j, correlation M i j ^ 2

theorem correlationSq_nonneg (M : CMatrix) : 0 ≤ correlationSq M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem pauli_hermitian (i : Fin 3) : (pauli i).IsHermitian := by
  change (pauli i)ᴴ = pauli i
  ext j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [pauli, pauliZ, Matrix.conjTranspose_apply, Complex.star_def]

theorem pauliPair_hermitian (i j : Fin 3) : (pauliPair i j).IsHermitian := by
  change (pauliPair i j)ᴴ = pauliPair i j
  ext p q
  have hi := (pauli_hermitian i).apply p.1 q.1
  have hj := (pauli_hermitian j).apply p.2 q.2
  simp only [Matrix.conjTranspose_apply, pauliPair, StarMul.star_mul]
  rw [hi, hj]
  ring

theorem trace_mul_hermitian_im {n : Type*} [Fintype n]
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (Matrix.trace (A*B)).im = 0 := by
  have h : star (Matrix.trace (A*B)) = Matrix.trace (A*B) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hA.eq, hB.eq,
      Matrix.trace_mul_comm]
  have hi := congrArg Complex.im h
  simp only [Complex.star_def, Complex.conj_im] at hi
  linarith

/-- Pauli completeness as an exact complex polynomial identity. -/
theorem correlation_trace_polynomial (M : CMatrix) :
    (∑ i : Fin 3, ∑ j : Fin 3, (Matrix.trace (M * pauliPair i j))^2) =
      4 * Matrix.trace (M*M) -
        2 * Matrix.trace (partialA M * partialA M) -
        2 * Matrix.trace (partialB M * partialB M) + (Matrix.trace M)^2 := by
  apply Complex.ext <;>
    simp [pauliPair, pauli, pauliZ, partialA, partialB,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fin.sum_univ_three, pow_two,
      Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im]
  all_goals ring

theorem correlationSq_purity (M : CMatrix) (hM : Density M) :
    correlationSq M = 4*(Matrix.trace (M*M)).re -
      2*(Matrix.trace (partialA M * partialA M)).re -
      2*(Matrix.trace (partialB M * partialB M)).re + 1 := by
  have hc : correlationSq M =
      (∑ i : Fin 3, ∑ j : Fin 3, (Matrix.trace (M * pauliPair i j))^2).re := by
    simp only [correlationSq, correlation, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have h := trace_mul_hermitian_im hM.1.1 (pauliPair_hermitian i j)
    simp [pow_two, Complex.mul_re, h]
  rw [hc, correlation_trace_polynomial, hM.2]
  simp [Complex.mul_re]

/-- The familiar Bloch-purity identity for the actual correlation observables. -/
theorem correlationSq_bloch (M : CMatrix) (hM : Density M) :
    correlationSq M = 4*(Matrix.trace (M*M)).re - 1 -
      blochSq (partialA M) - blochSq (partialB M) := by
  have hA := blochSq_trace_identity (partialA_psd hM.1).1
  have hB := blochSq_trace_identity (partialB_psd hM.1).1
  rw [trace_partialA, hM.2] at hA
  rw [trace_partialB, hM.2] at hB
  rw [correlationSq_purity M hM]
  norm_num at hA hB
  linarith

theorem correlationSq_purityDifference (M : CMatrix) (hM : Density M) :
    correlationSq M = 4*(purityDifference M).re + 1 +
      blochSq (partialA M) - blochSq (partialB M) := by
  have hA := blochSq_trace_identity (partialA_psd hM.1).1
  rw [trace_partialA, hM.2] at hA
  rw [correlationSq_bloch M hM]
  simp only [purityDifference, Complex.sub_re]
  norm_num at hA
  linarith

theorem blochState_correlations (a b : V3) (T : T3) :
    correlation (blochState a b T) = T := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [correlation, blochState, pauliPair, pauli, pauliZ, onAlice, onBob,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fin.sum_univ_three, Complex.mul_re, Complex.mul_im]
  all_goals ring

theorem blochState_correlationSq (a b : V3) (T : T3) :
    correlationSq (blochState a b T) = tSq T := by
  simp only [correlationSq, blochState_correlations, tSq]

end Milne
