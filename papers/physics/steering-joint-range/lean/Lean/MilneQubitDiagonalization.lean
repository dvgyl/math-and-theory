import MilneLocalUnitary

open scoped BigOperators Matrix ComplexOrder
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 16000
noncomputable section
namespace Milne

def qubitDiagonal (s t : ℝ) : Matrix Q Q ℂ :=
  Matrix.diagonal ![(((s+t)/2:ℝ):ℂ),(((s-t)/2:ℝ):ℂ)]

def qubitSwap : Matrix.unitaryGroup Q ℂ :=
  ⟨pauli 0, Matrix.mem_unitaryGroup_iff.mpr (by
    change pauli 0*(pauli 0)ᴴ = 1
    rw [(pauli_hermitian 0).eq]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pauli,Matrix.mul_apply,Matrix.one_apply,Fin.sum_univ_two])⟩

theorem qubitSwap_diagonal (a b : ℂ) :
    rigidityConj qubitSwap (Matrix.diagonal ![a,b]) = Matrix.diagonal ![b,a] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rigidityConj,qubitSwap,pauli,Matrix.mul_apply,
      Matrix.conjTranspose_apply,Matrix.diagonal_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]

/-- Ordered two-dimensional spectral normal form, valid for every Hermitian
qubit matrix, without positivity or a nondegeneracy assumption. -/
theorem qubit_ordered_diagonalization (A : Matrix Q Q ℂ) (hA : A.IsHermitian) :
    ∃ U : Matrix.unitaryGroup Q ℂ,
      rigidityConj U A = qubitDiagonal (Matrix.trace A).re (Real.sqrt (blochSq A)) := by
  let W := hA.eigenvectorUnitary
  have hs : hA.eigenvalues 0+hA.eigenvalues 1 = (Matrix.trace A).re := by
    simpa only [Fin.sum_univ_two] using (trace_eq_eigenvalue_sum hA).symm
  have hr : Real.sqrt (blochSq A) = |hA.eigenvalues 0-hA.eigenvalues 1| := by
    rw [blochSq_eigenvalue_difference hA,Real.sqrt_sq_eq_abs]
  have hdiag : rigidityConj W⁻¹ A =
      Matrix.diagonal ![(hA.eigenvalues 0:ℂ),(hA.eigenvalues 1:ℂ)] := by
    have hspec := hA.star_mul_self_mul_eq_diagonal
    have hf : Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) =
        Matrix.diagonal ![(hA.eigenvalues 0:ℂ),(hA.eigenvalues 1:ℂ)] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply,Function.comp_def]
    rw [hf] at hspec
    simpa [rigidityConj,W,Matrix.star_eq_conjTranspose] using hspec
  by_cases horder : hA.eigenvalues 1 ≤ hA.eigenvalues 0
  · have hgap : Real.sqrt (blochSq A) = hA.eigenvalues 0-hA.eigenvalues 1 := by
      rw [hr,abs_of_nonneg (sub_nonneg.mpr horder)]
    have h0 : hA.eigenvalues 0 = ((Matrix.trace A).re+Real.sqrt (blochSq A))/2 := by
      linarith
    have h1 : hA.eigenvalues 1 = ((Matrix.trace A).re-Real.sqrt (blochSq A))/2 := by
      linarith
    refine ⟨W⁻¹,?_⟩
    rw [hdiag,h0,h1]
    rfl
  · have hgap : Real.sqrt (blochSq A) = hA.eigenvalues 1-hA.eigenvalues 0 := by
      rw [hr,abs_of_neg (by linarith)]
      ring
    have h1 : hA.eigenvalues 1 = ((Matrix.trace A).re+Real.sqrt (blochSq A))/2 := by
      linarith
    have h0 : hA.eigenvalues 0 = ((Matrix.trace A).re-Real.sqrt (blochSq A))/2 := by
      linarith
    refine ⟨qubitSwap*W⁻¹,?_⟩
    rw [rigidityConj_mul,hdiag,qubitSwap_diagonal,h1,h0]
    rfl

theorem qubitDiagonal_one (c : ℝ) : qubitDiagonal 1 c = qubitState (c • geometryEz) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [qubitDiagonal,qubitState,spin,geometryEz,Pi.smul_apply,smul_eq_mul,
      Matrix.diagonal_apply,Matrix.one_apply,Complex.mul_re,Complex.mul_im]
  all_goals ring

theorem qubit_density_diagonalization (A : Matrix Q Q ℂ)
    (hA : A.IsHermitian) (htrace : Matrix.trace A = 1) :
    ∃ U : Matrix.unitaryGroup Q ℂ,
      rigidityConj U A = qubitState ((Real.sqrt (blochSq A)) • geometryEz) := by
  obtain ⟨U,hU⟩ := qubit_ordered_diagonalization A hA
  rw [htrace] at hU
  refine ⟨U,?_⟩
  simpa only [Complex.one_re,qubitDiagonal_one] using hU

end Milne

#print axioms Milne.qubit_ordered_diagonalization
