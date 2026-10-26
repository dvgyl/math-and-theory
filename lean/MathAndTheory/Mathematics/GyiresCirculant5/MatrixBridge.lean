module

/- This file comes from the order-five Gyires development.
The collection changes module paths and namespaces. See PROVENANCE.md for attribution. -/

public import MathAndTheory.Mathematics.GyiresCirculant5.MatrixProducts
public import MathAndTheory.Mathematics.GyiresCirculant5.FiniteIndices
public import Mathlib.LinearAlgebra.Matrix.Permanent
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# The permanent of a circulant

`permanent_succ` expands a permanent along its first column, and `permanent_circ` proves that
the permanent of `circ w` is the explicit polynomial `P5 w`.
-/

@[expose] public section

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open scoped BigOperators Matrix
namespace MathAndTheory.GyiresCirculant5

/-- Expansion by the first column, using an explicit finite equivalence. -/
theorem permanent_succ {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    A.permanent = ∑ p : Fin (n + 1), A p 0 *
      (A.submatrix (fun i : Fin n => Equiv.swap 0 p i.succ) Fin.succ).permanent := by
  unfold Matrix.permanent
  rw [← Equiv.sum_comp (Equiv.Perm.decomposeFin.symm)]
  simp only [Fintype.sum_prod_type, Fin.prod_univ_succ,
    Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_succ,
    Matrix.submatrix_apply, Finset.mul_sum]

theorem permanent_circ (w : Fin 5 → ℝ) : (circ w).permanent = P5 w := by
  simp (maxSteps := 4000000) only [permanent_succ, Fin.sum_univ_succ, Matrix.permanent_isEmpty,
    Matrix.submatrix_apply]
  norm_num [circ, P5, Equiv.swap_apply_def, Fin.ext_iff, Fin.succ,
    Fin.add_def, Fin.sub_def, Fin.neg_def]
  simp only [fin5_negative_one, fin5_negative_two, fin5_negative_three,
    fin5_negative_four]
  ring

end MathAndTheory.GyiresCirculant5
