module

public import MathAndTheory.Mathematics.Gyires.CirculantFive.PermanentGram
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

open Finset
open scoped BigOperators

namespace MathAndTheory.GyiresCirculant5.PermanentGram

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma bform_smul_left (t : ℝ) (a b : (n → n) → ℝ) :
    bform (t • a) b = t * bform a b := by
  simp only [bform, Pi.smul_apply, smul_eq_mul, mul_assoc, mul_sum]

lemma bform_smul_right (t : ℝ) (a b : (n → n) → ℝ) :
    bform a (t • b) = t * bform a b := by
  simp only [bform, Pi.smul_apply, smul_eq_mul, mul_sum]
  apply sum_congr rfl
  intro σ hσ
  apply sum_congr rfl
  intro φ hφ
  ring

/-- The permanent of a real Gram matrix is nonnegative. -/
theorem permanent_gram_nonneg (M : Matrix n n ℝ) :
    0 ≤ (M * M.transpose).permanent := by
  rw [permanent_mul_transpose]
  exact bform_self_nonneg _

/-- The squared permanent Cauchy–Schwarz inequality for real square matrices. -/
theorem permanent_mul_transpose_sq_le (M N : Matrix n n ℝ) :
    (M * N.transpose).permanent ^ 2 ≤
      (M * M.transpose).permanent * (N * N.transpose).permanent := by
  have h : ∀ t : ℝ, 0 ≤ bform (umono M) (umono M) * (t * t) +
      (-2 * bform (umono M) (umono N)) * t + bform (umono N) (umono N) := by
    intro t
    have ht := bform_self_nonneg (t • umono M - umono N)
    rw [bform_sub, bform_sub', bform_sub', bform_smul_left, bform_smul_right,
      bform_smul_right, bform_smul_left, bform_comm M N] at ht
    nlinarith
  have hd := discrim_le_zero h
  simp only [discrim] at hd
  simp only [permanent_mul_transpose]
  nlinarith

/-- The permanent Cauchy–Schwarz inequality for real square matrices. -/
theorem permanent_mul_transpose_abs_le (M N : Matrix n n ℝ) :
    |(M * N.transpose).permanent| ≤
      Real.sqrt ((M * M.transpose).permanent * (N * N.transpose).permanent) := by
  exact Real.abs_le_sqrt (permanent_mul_transpose_sq_le M N)

/-- A matrix square is bounded by the two Gram permanents. -/
theorem permanent_square_le_sqrt (A : Matrix n n ℝ) :
    (A * A).permanent ≤
      Real.sqrt ((A * A.transpose).permanent * (A.transpose * A).permanent) := by
  have h := permanent_mul_transpose_abs_le A A.transpose
  simp only [Matrix.transpose_transpose] at h
  exact (le_abs_self _).trans h

/-- Two Gram bounds imply the same bound for the matrix square. -/
theorem permanent_square_bound_of_gram_bounds (A : Matrix n n ℝ) (K B : ℝ)
    (hK : 0 ≤ K) (hleft : K * (A * A.transpose).permanent ≤ B)
    (hright : K * (A.transpose * A).permanent ≤ B) :
    K * (A * A).permanent ≤ B := by
  have h := permanent_gram_add_ge A A.transpose
  simp only [Matrix.transpose_transpose] at h
  have hscaled := mul_le_mul_of_nonneg_left h hK
  linarith

/-- A strict Gram bound gives a strict bound for the matrix square. -/
theorem permanent_square_lt_of_gram_bounds (A : Matrix n n ℝ) (K B : ℝ)
    (hK : 0 ≤ K) (hleft : K * (A * A.transpose).permanent < B)
    (hright : K * (A.transpose * A).permanent ≤ B) :
    K * (A * A).permanent < B := by
  have h := permanent_gram_add_ge A A.transpose
  simp only [Matrix.transpose_transpose] at h
  have hscaled := mul_le_mul_of_nonneg_left h hK
  linarith

/-- One strict Gram bound makes Gyires's combined inequality strict. -/
theorem gyires_lt_of_strong (A : Matrix n n ℝ) (K : ℝ)
    (hK : 0 ≤ K)
    (hleft : K * (A * A.transpose).permanent < A.permanent ^ 2)
    (hright : K * (A.transpose * A).permanent ≤ A.permanent ^ 2) :
    K * ((A * A.transpose).permanent + (A.transpose * A).permanent +
      2 * (A * A).permanent) < 4 * A.permanent ^ 2 := by
  have h := permanent_gram_add_ge A A.transpose
  simp only [Matrix.transpose_transpose] at h
  have hscaled := mul_le_mul_of_nonneg_left h hK
  linarith

end MathAndTheory.GyiresCirculant5.PermanentGram
