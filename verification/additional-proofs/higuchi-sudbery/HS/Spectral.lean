import HS.Definitions
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open scoped BigOperators
open Matrix

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

namespace HS

/-- The Hermitian Gram matrix of each balanced flattening. -/
theorem reduced_isHermitian (cut : Fin 3) (z : Fin 16 → ℂ) :
    (reduced cut z).IsHermitian :=
  Matrix.isHermitian_mul_conjTranspose_self _

/-- Actual real eigenvalues of the two-qubit reduced density matrix. -/
noncomputable def cutEigenvalues (cut : Fin 3) (z : Fin 16 → ℂ) : Fin 4 → ℝ :=
  (reduced_isHermitian cut z).eigenvalues

theorem cutEigenvalues_nonneg (cut : Fin 3) (z : Fin 16 → ℂ) (i : Fin 4) :
    0 ≤ cutEigenvalues cut z i :=
  Matrix.eigenvalues_self_mul_conjTranspose_nonneg _ _

/-- Newton's third identity, checked as a polynomial identity for arbitrary matrices. -/
theorem newton_three (M : Matrix (Fin 4) (Fin 4) ℂ) :
    6 * principalE3 M =
      (Matrix.trace M) ^ 3 - 3 * Matrix.trace M * Matrix.trace (M * M) +
        2 * Matrix.trace (M * M * M) := by
  simp only [principalE3, minor3, Matrix.det_fin_three, Matrix.submatrix_apply,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_succ]
  norm_num [Fin.succAbove]
  ring

/-- The trace of a power equals the corresponding eigenvalue power sum. -/
theorem trace_pow_eq_sum_eigenvalues {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (hM : M.IsHermitian) (k : ℕ) :
    Matrix.trace (M ^ k) = ∑ i, ((hM.eigenvalues i : ℂ) ^ k) := by
  conv_lhs => rw [hM.spectral_theorem, ← map_pow, Unitary.conjStarAlgAut_apply,
    Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul,
    Matrix.diagonal_pow, Matrix.trace_diagonal]
  rfl

/-- Cauchy--Binet for the third principal coefficient of a four-by-four Gram matrix. -/
theorem principalE3_eq_trace_adjugate (M : Matrix (Fin 4) (Fin 4) ℂ) :
    principalE3 M = Matrix.trace M.adjugate := by
  simp only [principalE3, Matrix.trace, Matrix.diag]
  apply Finset.sum_congr rfl
  intro r _
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  fin_cases r <;> norm_num [minor3]

theorem principalE3_gram (M : Matrix (Fin 4) (Fin 4) ℂ) :
    principalE3 (M * M.conjTranspose) =
      ((∑ r : Fin 4, ∑ c : Fin 4, Complex.normSq (minor3 M r c) : ℝ) : ℂ) := by
  rw [principalE3_eq_trace_adjugate, Matrix.adjugate_mul_distrib,
    ← Matrix.adjugate_conjTranspose]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro c _
  rw [Complex.normSq_eq_conj_mul_self, Matrix.adjugate_fin_succ_eq_det_submatrix]
  fin_cases r <;> fin_cases c <;> norm_num [minor3, map_mul, map_neg]

theorem trace_reduced (cut : Fin 3) (z : Fin 16 → ℂ) :
    Matrix.trace (reduced cut z) = (stateNormSq z : ℂ) := by
  simp only [reduced, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj,
    stateNormSq, Complex.ofReal_sum]
  fin_cases cut <;> norm_num [flatten, flattenIndex, Fin.sum_univ_succ] <;> ring

theorem cutEigenvalues_sum (cut : Fin 3) (z : Fin 16 → ℂ) :
    ∑ i, cutEigenvalues cut z i = stateNormSq z := by
  have h := (reduced_isHermitian cut z).trace_eq_sum_eigenvalues
  change Matrix.trace (reduced cut z) = ∑ i, (cutEigenvalues cut z i : ℂ) at h
  rw [trace_reduced] at h
  have h' := congrArg Complex.re h
  simpa [cutEigenvalues] using h'.symm

theorem cutEigenvalues_pow_sum (cut : Fin 3) (z : Fin 16 → ℂ) (k : ℕ) :
    ∑ i, cutEigenvalues cut z i ^ k = (Matrix.trace (reduced cut z ^ k)).re := by
  have h := trace_pow_eq_sum_eigenvalues (reduced cut z) (reduced_isHermitian cut z) k
  have h' := congrArg Complex.re h
  simpa only [Complex.re_sum, ← Complex.ofReal_pow, Complex.ofReal_re, cutEigenvalues]
    using h'.symm

theorem cutEigenvalues_square_sum (z : Fin 16 → ℂ) :
    (∑ cut : Fin 3, ∑ i : Fin 4, cutEigenvalues cut z i ^ 2) = puritySum z := by
  unfold puritySum
  apply Finset.sum_congr rfl
  intro cut _
  simpa only [pow_two] using cutEigenvalues_pow_sum cut z 2

/-- The trace/eigenvalue version of Cauchy--Binet and Newton's identity for one cut. -/
theorem cut_moment_identity (cut : Fin 3) (z : Fin 16 → ℂ) :
    6 * (∑ r : Fin 4, ∑ c : Fin 4, Complex.normSq (minor3 (flatten cut z) r c)) =
      stateNormSq z ^ 3 - 3 * stateNormSq z * (∑ i, cutEigenvalues cut z i ^ 2) +
        2 * (∑ i, cutEigenvalues cut z i ^ 3) := by
  have h := newton_three (reduced cut z)
  have h2 : Matrix.trace (reduced cut z * reduced cut z) =
      ∑ i, (((reduced_isHermitian cut z).eigenvalues i : ℂ) ^ 2) := by
    simpa only [pow_two] using
      trace_pow_eq_sum_eigenvalues (reduced cut z) (reduced_isHermitian cut z) 2
  have h3 : Matrix.trace (reduced cut z * reduced cut z * reduced cut z) =
      ∑ i, (((reduced_isHermitian cut z).eigenvalues i : ℂ) ^ 3) := by
    simpa only [pow_succ, pow_zero, one_mul] using
      trace_pow_eq_sum_eigenvalues (reduced cut z) (reduced_isHermitian cut z) 3
  rw [show principalE3 (reduced cut z) = _ from principalE3_gram (flatten cut z),
    trace_reduced, h2, h3] at h
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_sum] at h
  exact_mod_cast h

/-- The exact total second/third moment identity for all balanced cuts. -/
theorem total_moment_identity (z : Fin 16 → ℂ) :
    6 * minorSum z = 3 * stateNormSq z ^ 3 - 3 * stateNormSq z * puritySum z +
      2 * (∑ cut : Fin 3, ∑ i : Fin 4, cutEigenvalues cut z i ^ 3) := by
  have h0 := cut_moment_identity 0 z
  have h1 := cut_moment_identity 1 z
  have h2 := cut_moment_identity 2 z
  rw [← cutEigenvalues_square_sum]
  simp only [minorSum, Fin.sum_univ_three] at *
  linarith

/-- Normalized matrix minors provide the upper bound on the total cubic spectral moment. -/
theorem cubic_moment_bound (z : Fin 16 → ℂ) (hn : stateNormSq z = 1)
    (hm : minorSum z ≤ (5 : ℝ) / 36) :
    (∑ cut : Fin 3, ∑ i : Fin 4, cutEigenvalues cut z i ^ 3) ≤
      (3 : ℝ) / 2 * (∑ cut : Fin 3, ∑ i : Fin 4, cutEigenvalues cut z i ^ 2) -
        (13 : ℝ) / 12 := by
  have h := total_moment_identity z
  rw [hn, one_pow, mul_one] at h
  rw [cutEigenvalues_square_sum]
  linarith

/-- The third elementary symmetric polynomial of four real numbers. -/
def elementaryThree (l : Fin 4 → ℝ) : ℝ :=
  l 0 * l 1 * l 2 + l 0 * l 1 * l 3 + l 0 * l 2 * l 3 + l 1 * l 2 * l 3

theorem elementaryThree_newton (l : Fin 4 → ℝ) :
    6 * elementaryThree l = (∑ i, l i) ^ 3 -
      3 * (∑ i, l i) * (∑ i, l i ^ 2) + 2 * (∑ i, l i ^ 3) := by
  simp only [elementaryThree, Fin.sum_univ_four]
  ring

/-- The coefficient certificate concerns the actual third elementary symmetric
polynomial of each marginal's eigenvalues, with no change of normalization. -/
theorem elementaryThree_cut_eq_minors (cut : Fin 3) (z : Fin 16 → ℂ) :
    elementaryThree (cutEigenvalues cut z) =
      ∑ r : Fin 4, ∑ c : Fin 4, Complex.normSq (minor3 (flatten cut z) r c) := by
  have h := elementaryThree_newton (cutEigenvalues cut z)
  rw [cutEigenvalues_sum] at h
  have hc := cut_moment_identity cut z
  linarith

theorem elementaryThree_sum_eq_minorSum (z : Fin 16 → ℂ) :
    (∑ cut : Fin 3, elementaryThree (cutEigenvalues cut z)) = minorSum z := by
  simp only [elementaryThree_cut_eq_minors, minorSum]

end HS
