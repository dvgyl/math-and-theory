import MilneCore
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

open scoped BigOperators Matrix ComplexOrder
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

noncomputable section

namespace Milne

/-- The squared Hilbert--Schmidt norm of an actual complex matrix. -/
def matrixHsSq {n : Type*} [Fintype n] (A : Matrix n n ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (A i j)

/-- The trace norm of a Hermitian matrix, defined as the sum of the absolute
values of its real eigenvalues. No positivity or nonsingularity is required. -/
def hermitianTraceNorm {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) : ℝ :=
  ∑ i, |hA.eigenvalues i|

theorem matrixHsSq_nonneg {n : Type*} [Fintype n] (A : Matrix n n ℂ) :
    0 ≤ matrixHsSq A := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _

theorem matrixHsSq_eq_zero_iff {n : Type*} [Fintype n] (A : Matrix n n ℂ) :
    matrixHsSq A = 0 ↔ A = 0 := by
  constructor
  · intro h
    ext i j
    have hrow : (∑ k, Complex.normSq (A i k)) ≤ matrixHsSq A :=
      Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun l _ =>
        Complex.normSq_nonneg _) (Finset.mem_univ i)
    have hij : Complex.normSq (A i j) ≤ ∑ k, Complex.normSq (A i k) :=
      Finset.single_le_sum (fun k _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
    have hz : Complex.normSq (A i j) = 0 := by
      rw [h] at hrow
      linarith [Complex.normSq_nonneg (A i j)]
    exact Complex.normSq_eq_zero.mp hz
  · intro h
    simp [h,matrixHsSq]

theorem matrixHsSq_eq_trace {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) :
    matrixHsSq A = (Matrix.trace (Aᴴ * A)).re := by
  simp only [matrixHsSq, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp [Complex.normSq_apply, Complex.mul_re]

theorem hermitian_matrixHsSq_eq_trace {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    matrixHsSq A = (Matrix.trace (A * A)).re := by
  rw [matrixHsSq_eq_trace, hA.eq]

theorem trace_unitary_conj {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix.unitaryGroup n ℂ) (A : Matrix n n ℂ) :
    Matrix.trace ((U : Matrix n n ℂ) * A * (star U : Matrix n n ℂ)) =
      Matrix.trace A := by
  rw [Matrix.trace_mul_cycle, unitary.coe_star_mul_self, one_mul]

theorem hermitian_trace_eq_sum_eigenvalues {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (Matrix.trace A).re = ∑ i, hA.eigenvalues i := by
  exact trace_eq_eigenvalue_sum hA

theorem hermitian_matrixHsSq_eq_sum_sq {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    matrixHsSq A = ∑ i, (hA.eigenvalues i)^2 := by
  rw [hermitian_matrixHsSq_eq_trace hA, trace_sq_eq_eigenvalue_sq_sum hA]

theorem hermitianTraceNorm_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) : 0 ≤ hermitianTraceNorm hA := by
  exact Finset.sum_nonneg fun i _ => abs_nonneg _

/-- The genuine trace norm is bounded by the Hilbert--Schmidt norm, with the
dimension factor. This includes all rank-deficient Hermitian matrices. -/
theorem hermitianTraceNorm_sq_le_card_mul_hs {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (hermitianTraceNorm hA)^2 ≤ Fintype.card n * matrixHsSq A := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset n)
    (fun _ => (1 : ℝ)) (fun i => |hA.eigenvalues i|)
  simpa [hermitianTraceNorm, hermitian_matrixHsSq_eq_sum_sq hA, sq_abs] using h

theorem hermitianTraceNorm_sq_le_four_hs {A : CMatrix} (hA : A.IsHermitian) :
    (hermitianTraceNorm hA)^2 ≤ 4 * matrixHsSq A := by
  simpa using hermitianTraceNorm_sq_le_card_mul_hs hA

end Milne
