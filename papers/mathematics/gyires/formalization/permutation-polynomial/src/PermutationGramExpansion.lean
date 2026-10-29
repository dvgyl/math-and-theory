module

public import OffsetExpansion
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace MathAndTheory.Gyires.PermutationMatrixBridge

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def shiftMatrix (p : Equiv.Perm ι) (k : ℤ) : Matrix ι ι ℝ :=
  (p^k).permMatrix ℝ

omit [Fintype ι] in
theorem shiftMatrix_zero (p : Equiv.Perm ι) : shiftMatrix p 0 = 1 := by
  simp [shiftMatrix]

theorem shiftMatrix_mul (p : Equiv.Perm ι) (j k : ℤ) :
    shiftMatrix p j * shiftMatrix p k = shiftMatrix p (j + k) := by
  simp only [shiftMatrix]
  rw [← Matrix.permMatrix_mul, ← zpow_add]
  rw [add_comm]

omit [Fintype ι] in
theorem shiftMatrix_transpose (p : Equiv.Perm ι) (k : ℤ) :
    (shiftMatrix p k).transpose = shiftMatrix p (-k) := by
  simp [shiftMatrix]

theorem polynomialMatrix_eq_shifts (p : Equiv.Perm ι) (a b c : ℝ) :
    polynomialMatrix p a b c =
      a • shiftMatrix p 0 + b • shiftMatrix p 1 + c • shiftMatrix p 2 := by
  simp [polynomialMatrix, shiftMatrix, pow_two, Matrix.permMatrix_mul]

theorem polynomialMatrix_gram (p : Equiv.Perm ι) (a b c : ℝ) :
    polynomialMatrix p a b c * (polynomialMatrix p a b c).transpose =
      (a^2 + b^2 + c^2) • (1 : Matrix ι ι ℝ) +
      (b*(a+c)) • shiftMatrix p (-1) + (b*(a+c)) • shiftMatrix p 1 +
      (a*c) • shiftMatrix p (-2) + (a*c) • shiftMatrix p 2 := by
  rw [polynomialMatrix_eq_shifts]
  simp only [Matrix.transpose_add, Matrix.transpose_smul, shiftMatrix_transpose,
    add_mul, mul_add, smul_mul_assoc, mul_smul_comm, shiftMatrix_mul]
  norm_num only
  rw [shiftMatrix_zero]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem polynomialMatrix_normal (p : Equiv.Perm ι) (a b c : ℝ) :
    polynomialMatrix p a b c * (polynomialMatrix p a b c).transpose =
      (polynomialMatrix p a b c).transpose * polynomialMatrix p a b c := by
  rw [polynomialMatrix_eq_shifts]
  simp only [Matrix.transpose_add, Matrix.transpose_smul, shiftMatrix_transpose,
    add_mul, mul_add, smul_mul_assoc, mul_smul_comm, shiftMatrix_mul]
  norm_num only
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

#print axioms shiftMatrix_zero
#print axioms shiftMatrix_mul
#print axioms shiftMatrix_transpose
#print axioms polynomialMatrix_eq_shifts
#print axioms polynomialMatrix_gram
#print axioms polynomialMatrix_normal

end MathAndTheory.Gyires.PermutationMatrixBridge
