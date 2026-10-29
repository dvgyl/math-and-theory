import MilneCore

open scoped BigOperators Matrix ComplexOrder
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Milne

/-- The qubit Bloch length in terms of matrix traces, for any Hermitian matrix. -/
theorem blochSq_trace_identity {A : Matrix Q Q ℂ} (hA : A.IsHermitian) :
    blochSq A = 2 * (Matrix.trace (A*A)).re - (Matrix.trace A).re^2 := by
  have h0 := hermitian_diag_im hA 0
  have h1 := hermitian_diag_im hA 1
  have ho : A 1 0 = star (A 0 1) := by simpa using (hA.apply 1 0).symm
  simp only [blochSq, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two,
    ho, Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.add_re,
    Complex.mul_re, Complex.normSq_apply, h0, h1]
  ring

/-- Both eigenvalues of a Hermitian qubit matrix are determined by its trace
and Bloch length; no ordering convention for Mathlib's spectrum is needed. -/
theorem blochSq_eigenvalue_difference {A : Matrix Q Q ℂ} (hA : A.IsHermitian) :
    blochSq A = (hA.eigenvalues 0 - hA.eigenvalues 1)^2 := by
  rw [blochSq_trace_identity hA, trace_sq_eq_eigenvalue_sq_sum hA,
    trace_eq_eigenvalue_sum hA]
  simp only [Fin.sum_univ_two]
  ring

/-- The same invariant in determinant form. -/
theorem blochSq_det_identity {A : Matrix Q Q ℂ} (hA : A.IsHermitian) :
    blochSq A = (Matrix.trace A).re^2 - 4*A.det.re := by
  have h0 := hermitian_diag_im hA 0
  have h1 := hermitian_diag_im hA 1
  have ho : A 1 0 = star (A 0 1) := by simpa using (hA.apply 1 0).symm
  simp only [blochSq, Matrix.trace, Matrix.diag, Matrix.det_fin_two, Fin.sum_univ_two,
    ho, Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.add_re,
    Complex.sub_re, Complex.mul_re, Complex.normSq_apply, h0, h1]
  ring

theorem hermitian_det_im {A : Matrix Q Q ℂ} (hA : A.IsHermitian) : A.det.im = 0 := by
  have h0 := hermitian_diag_im hA 0
  have h1 := hermitian_diag_im hA 1
  have ho : A 1 0 = star (A 0 1) := by simpa using (hA.apply 1 0).symm
  simp only [Matrix.det_fin_two, ho, Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.sub_im, Complex.mul_im, h0, h1]
  ring

/-- Actual lower operator bound for a trace-one Hermitian qubit matrix. -/
theorem qubit_lower_operator_bound {B : Matrix Q Q ℂ} (hB : B.IsHermitian)
    (htrace : Matrix.trace B = 1) :
    ((2:ℂ) • B - (((1 - Real.sqrt (blochSq B) : ℝ) : ℂ) •
      (1 : Matrix Q Q ℂ))).PosSemidef := by
  let r : ℝ := Real.sqrt (blochSq B)
  let U : Matrix Q Q ℂ := hB.eigenvectorUnitary
  let D : Matrix Q Q ℂ := Matrix.diagonal (RCLike.ofReal ∘ hB.eigenvalues)
  have hr : r = |hB.eigenvalues 0 - hB.eigenvalues 1| := by
    dsimp [r]
    rw [blochSq_eigenvalue_difference hB, Real.sqrt_sq_eq_abs]
  have hs : hB.eigenvalues 0 + hB.eigenvalues 1 = 1 := by
    have h := trace_eq_eigenvalue_sum hB
    rw [htrace] at h
    simpa only [Complex.one_re, Fin.sum_univ_two] using h.symm
  have he : ∀ i, 0 ≤ 2 * hB.eigenvalues i - (1-r) := by
    intro i
    have hlo := neg_abs_le (hB.eigenvalues 0 - hB.eigenvalues 1)
    have hhi := le_abs_self (hB.eigenvalues 0 - hB.eigenvalues 1)
    rw [← hr] at hlo hhi
    fin_cases i
    · change 0 ≤ 2 * hB.eigenvalues 0 - (1-r)
      linarith
    · change 0 ≤ 2 * hB.eigenvalues 1 - (1-r)
      linarith
  have hd : (Matrix.diagonal (fun i => ((2*hB.eigenvalues i-(1-r):ℝ):ℂ))).PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    exact RCLike.ofReal_nonneg.mpr (he i)
  have hde : Matrix.diagonal (fun i => ((2*hB.eigenvalues i-(1-r):ℝ):ℂ)) =
      (2:ℂ) • D - ((1-r:ℝ):ℂ) • (1 : Matrix Q Q ℂ) := by
    ext i j
    by_cases hij : i = j <;>
      simp [D, hij, Matrix.diagonal_apply, Matrix.one_apply]
  have h := hd.mul_mul_conjTranspose_same U
  rw [hde, mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.smul_mul, mul_one] at h
  have hspec : U * D * Uᴴ = B := by
    simpa [U, D, ← Matrix.star_eq_conjTranspose] using hB.spectral_theorem.symm
  have hu : U * Uᴴ = (1 : Matrix Q Q ℂ) := by
    simp [U, ← Matrix.star_eq_conjTranspose]
  rw [hspec, hu] at h
  exact h

theorem qubit_density_lower_operator_bound {B : Matrix Q Q ℂ} (hB : B.PosSemidef)
    (htrace : Matrix.trace B = 1) :
    ((2:ℂ) • B - (((1 - Real.sqrt (blochSq B) : ℝ) : ℂ) •
      (1 : Matrix Q Q ℂ))).PosSemidef :=
  qubit_lower_operator_bound hB.1 htrace

theorem qubit_bloch_le_one {B : Matrix Q Q ℂ} (hB : B.PosSemidef)
    (htrace : Matrix.trace B = 1) : Real.sqrt (blochSq B) ≤ 1 := by
  have hb := blochSq_psd_le hB
  rw [htrace] at hb
  have hr := Real.sq_sqrt (blochSq_nonneg B)
  have hn := Real.sqrt_nonneg (blochSq B)
  norm_num at hb
  nlinarith

end Milne
