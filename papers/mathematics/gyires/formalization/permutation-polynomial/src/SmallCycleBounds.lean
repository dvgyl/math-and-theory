module

public import PermutationGramExpansion
public import MathAndTheory.Mathematics.Gyires.DimensionConstant
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.IntervalCases

@[expose] public section

namespace MathAndTheory.Gyires.PermutationCycle

open Matrix Equiv
open MathAndTheory.Gyires.PermutationMatrixBridge

theorem cycle_order_two_permanent (a b c : ℝ) :
    (polynomialMatrix (finRotate 2) a b c).permanent = (a+c)^2+b^2 := by
  have hrotate : finRotate 2 = Equiv.swap (0 : Fin 2) 1 := by decide
  have hperms : (Finset.univ : Finset (Equiv.Perm (Fin 2))) =
      {1, Equiv.swap 0 1} := by decide
  have hne : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 := by decide
  rw [hrotate]
  norm_num [Matrix.permanent, hperms, hne, polynomialMatrix, Matrix.mul_apply,
    Matrix.smul_apply, Matrix.add_apply, Fin.sum_univ_succ, Fin.prod_univ_succ,
    Equiv.Perm.permMatrix, Matrix.one_apply, pow_two]

theorem cycle_order_two_gram_matrix (a b c : ℝ) :
    polynomialMatrix (finRotate 2) a b c * (polynomialMatrix (finRotate 2) a b c).transpose =
      polynomialMatrix (finRotate 2) ((a+c)^2+b^2) (2*b*(a+c)) 0 := by
  have hrotate : finRotate 2 = Equiv.swap (0 : Fin 2) 1 := by decide
  rw [hrotate]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [polynomialMatrix, pow_two, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.smul_apply, Matrix.add_apply, Fin.sum_univ_succ, Equiv.Perm.permMatrix,
      Matrix.one_apply] <;> ring

theorem cycle_order_two_gram_gap (a b c : ℝ) :
    let A := polynomialMatrix (finRotate 2) a b c
    A.permanent^2 - dimensionConstant 2 * (A*A.transpose).permanent =
      (((a+c)^2-b^2)^2)/2 := by
  dsimp only
  rw [cycle_order_two_gram_matrix, cycle_order_two_permanent, cycle_order_two_permanent]
  norm_num [dimensionConstant]
  ring

theorem cycle_order_zero_left_gram (a b c : ℝ) :
    let A := polynomialMatrix (finRotate 0) a b c
    dimensionConstant 0 * (A*A.transpose).permanent = A.permanent^2 := by
  simp [dimensionConstant, Matrix.permanent_isEmpty]

theorem cycle_order_one_left_gram (a b c : ℝ) :
    let A := polynomialMatrix (finRotate 1) a b c
    dimensionConstant 1 * (A*A.transpose).permanent = A.permanent^2 := by
  simp [dimensionConstant, polynomialMatrix, Matrix.permanent_unique, Matrix.mul_apply,
    Matrix.smul_apply, Matrix.add_apply, pow_two]

theorem cycle_order_two_left_gram (a b c : ℝ) :
    let A := polynomialMatrix (finRotate 2) a b c
    dimensionConstant 2 * (A*A.transpose).permanent ≤ A.permanent^2 := by
  have h := cycle_order_two_gram_gap a b c
  have hp : 0 ≤ (((a+c)^2-b^2)^2)/2 := div_nonneg (sq_nonneg _) (by norm_num)
  dsimp only at h ⊢
  linarith

theorem cycle_small_order_both_gram (n : ℕ) (hn : n ≤ 2) (a b c : ℝ) :
    let A := polynomialMatrix (finRotate n) a b c
    dimensionConstant n * (A*A.transpose).permanent ≤ A.permanent^2 ∧
      dimensionConstant n * (A.transpose*A).permanent ≤ A.permanent^2 := by
  have hleft : dimensionConstant n *
      (polynomialMatrix (finRotate n) a b c * (polynomialMatrix (finRotate n) a b c).transpose).permanent ≤
      (polynomialMatrix (finRotate n) a b c).permanent^2 := by
    interval_cases n
    · exact (cycle_order_zero_left_gram a b c).le
    · exact (cycle_order_one_left_gram a b c).le
    · exact cycle_order_two_left_gram a b c
  refine ⟨hleft, ?_⟩
  rw [← polynomialMatrix_normal]
  exact hleft

end MathAndTheory.Gyires.PermutationCycle
