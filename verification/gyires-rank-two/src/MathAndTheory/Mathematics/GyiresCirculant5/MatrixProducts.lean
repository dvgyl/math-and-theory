module

/- See PROVENANCE.md for source attribution and modifications. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.Definitions
public import MathAndTheory.Mathematics.GyiresCirculant5.FiniteIndices
public import Mathlib.LinearAlgebra.Matrix.Permanent
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Products of circulants

For the circulant `circ w`: `circ w * (circ w)ᵀ = (circ w)ᵀ * circ w = circ (gram w)` and
`circ w * circ w = circ (conv w)`. Each identity is checked entry by entry.
-/

@[expose] public section

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open scoped BigOperators Matrix
namespace MathAndTheory.GyiresCirculant5

@[simp] private theorem product_neg_two_val : (-2 : Fin 5).val = 3 := rfl
@[simp] private theorem product_neg_three_val : (-3 : Fin 5).val = 2 := rfl
@[simp] private theorem product_neg_four_val : (-4 : Fin 5).val = 1 := rfl

theorem circ_mul_transpose (w : Fin 5 → ℝ) :
    circ w * (circ w)ᵀ = circ (gram w) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Matrix.transpose_apply, circ, gram, Fin.sum_univ_succ,
      Fin.succ, Fin.add_def, Fin.sub_def, Fin.neg_def, Fin.ext_iff] <;> ring

theorem transpose_mul_circ (w : Fin 5 → ℝ) :
    (circ w)ᵀ * circ w = circ (gram w) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Matrix.transpose_apply, circ, gram, Fin.sum_univ_succ,
      Fin.succ, Fin.add_def, Fin.sub_def, Fin.neg_def, Fin.ext_iff] <;> ring

theorem circ_mul_self (w : Fin 5 → ℝ) :
    circ w * circ w = circ (conv w) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, circ, conv, Fin.sum_univ_succ,
      Fin.succ, Fin.add_def, Fin.sub_def, Fin.neg_def, Fin.ext_iff] <;> ring

end MathAndTheory.GyiresCirculant5
