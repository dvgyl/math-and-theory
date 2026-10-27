module
public import MathAndTheory.Mathematics.GyiresCirculant5.MatrixBridge
public import Mathlib.Tactic.Ring
@[expose] public section
open scoped BigOperators
namespace MathAndTheory.Gyires.CirculantSix
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
def matrix (w : Fin 6 → ℝ) : Matrix (Fin 6) (Fin 6) ℝ := fun i j => w (j - i)
def permanentPolynomial (w : Fin 6 → ℝ) : ℝ :=
  1 * (w 5) ^ 6 +
  1 * (w 4) ^ 6 +
  6 * (w 3) * (w 4) ^ 4 * (w 5) +
  9 * (w 3) ^ 2 * (w 4) ^ 2 * (w 5) ^ 2 +
  2 * (w 3) ^ 3 * (w 5) ^ 3 +
  1 * (w 3) ^ 6 +
  6 * (w 2) * (w 4) ^ 3 * (w 5) ^ 2 +
  12 * (w 2) * (w 3) * (w 4) * (w 5) ^ 3 +
  6 * (w 2) * (w 3) ^ 4 * (w 4) +
  3 * (w 2) ^ 2 * (w 5) ^ 4 +
  9 * (w 2) ^ 2 * (w 3) ^ 2 * (w 4) ^ 2 +
  6 * (w 2) ^ 2 * (w 3) ^ 3 * (w 5) +
  2 * (w 2) ^ 3 * (w 4) ^ 3 +
  12 * (w 2) ^ 3 * (w 3) * (w 4) * (w 5) +
  3 * (w 2) ^ 4 * (w 5) ^ 2 +
  1 * (w 2) ^ 6 +
  6 * (w 1) * (w 4) ^ 2 * (w 5) ^ 3 +
  6 * (w 1) * (w 3) * (w 5) ^ 4 +
  6 * (w 1) * (w 3) ^ 3 * (w 4) ^ 2 +
  6 * (w 1) * (w 3) ^ 4 * (w 5) +
  12 * (w 1) * (w 2) * (w 3) * (w 4) ^ 3 +
  24 * (w 1) * (w 2) * (w 3) ^ 2 * (w 4) * (w 5) +
  18 * (w 1) * (w 2) ^ 2 * (w 4) ^ 2 * (w 5) +
  12 * (w 1) * (w 2) ^ 2 * (w 3) * (w 5) ^ 2 +
  6 * (w 1) * (w 2) ^ 4 * (w 3) +
  3 * (w 1) ^ 2 * (w 4) ^ 4 +
  12 * (w 1) ^ 2 * (w 3) * (w 4) ^ 2 * (w 5) +
  9 * (w 1) ^ 2 * (w 3) ^ 2 * (w 5) ^ 2 +
  18 * (w 1) ^ 2 * (w 2) * (w 4) * (w 5) ^ 2 +
  9 * (w 1) ^ 2 * (w 2) ^ 2 * (w 3) ^ 2 +
  6 * (w 1) ^ 2 * (w 2) ^ 3 * (w 4) +
  2 * (w 1) ^ 3 * (w 5) ^ 3 +
  2 * (w 1) ^ 3 * (w 3) ^ 3 +
  12 * (w 1) ^ 3 * (w 2) * (w 3) * (w 4) +
  6 * (w 1) ^ 3 * (w 2) ^ 2 * (w 5) +
  3 * (w 1) ^ 4 * (w 4) ^ 2 +
  6 * (w 1) ^ 4 * (w 3) * (w 5) +
  1 * (w 1) ^ 6 +
  6 * (w 0) * (w 4) * (w 5) ^ 4 +
  6 * (w 0) * (w 3) ^ 2 * (w 4) ^ 3 +
  12 * (w 0) * (w 3) ^ 3 * (w 4) * (w 5) +
  6 * (w 0) * (w 2) * (w 4) ^ 4 +
  24 * (w 0) * (w 2) * (w 3) * (w 4) ^ 2 * (w 5) +
  18 * (w 0) * (w 2) * (w 3) ^ 2 * (w 5) ^ 2 +
  12 * (w 0) * (w 2) ^ 2 * (w 4) * (w 5) ^ 2 +
  6 * (w 0) * (w 2) ^ 3 * (w 3) ^ 2 +
  6 * (w 0) * (w 2) ^ 4 * (w 4) +
  12 * (w 0) * (w 1) * (w 4) ^ 3 * (w 5) +
  24 * (w 0) * (w 1) * (w 3) * (w 4) * (w 5) ^ 2 +
  12 * (w 0) * (w 1) * (w 2) * (w 5) ^ 3 +
  12 * (w 0) * (w 1) * (w 2) * (w 3) ^ 3 +
  24 * (w 0) * (w 1) * (w 2) ^ 2 * (w 3) * (w 4) +
  12 * (w 0) * (w 1) * (w 2) ^ 3 * (w 5) +
  18 * (w 0) * (w 1) ^ 2 * (w 3) ^ 2 * (w 4) +
  12 * (w 0) * (w 1) ^ 2 * (w 2) * (w 4) ^ 2 +
  24 * (w 0) * (w 1) ^ 2 * (w 2) * (w 3) * (w 5) +
  12 * (w 0) * (w 1) ^ 3 * (w 4) * (w 5) +
  6 * (w 0) * (w 1) ^ 4 * (w 2) +
  9 * (w 0) ^ 2 * (w 4) ^ 2 * (w 5) ^ 2 +
  6 * (w 0) ^ 2 * (w 3) * (w 5) ^ 3 +
  3 * (w 0) ^ 2 * (w 3) ^ 4 +
  12 * (w 0) ^ 2 * (w 2) * (w 3) ^ 2 * (w 4) +
  9 * (w 0) ^ 2 * (w 2) ^ 2 * (w 4) ^ 2 +
  18 * (w 0) ^ 2 * (w 2) ^ 2 * (w 3) * (w 5) +
  18 * (w 0) ^ 2 * (w 1) * (w 3) * (w 4) ^ 2 +
  12 * (w 0) ^ 2 * (w 1) * (w 3) ^ 2 * (w 5) +
  24 * (w 0) ^ 2 * (w 1) * (w 2) * (w 4) * (w 5) +
  9 * (w 0) ^ 2 * (w 1) ^ 2 * (w 5) ^ 2 +
  9 * (w 0) ^ 2 * (w 1) ^ 2 * (w 2) ^ 2 +
  6 * (w 0) ^ 2 * (w 1) ^ 3 * (w 3) +
  2 * (w 0) ^ 3 * (w 4) ^ 3 +
  12 * (w 0) ^ 3 * (w 3) * (w 4) * (w 5) +
  6 * (w 0) ^ 3 * (w 2) * (w 5) ^ 2 +
  2 * (w 0) ^ 3 * (w 2) ^ 3 +
  12 * (w 0) ^ 3 * (w 1) * (w 2) * (w 3) +
  6 * (w 0) ^ 3 * (w 1) ^ 2 * (w 4) +
  3 * (w 0) ^ 4 * (w 3) ^ 2 +
  6 * (w 0) ^ 4 * (w 2) * (w 4) +
  6 * (w 0) ^ 4 * (w 1) * (w 5) +
  1 * (w 0) ^ 6
@[simp] private theorem neg_1 : (-1 : Fin 6) = 5 := by decide
@[simp] private theorem neg_2 : (-2 : Fin 6) = 4 := by decide
@[simp] private theorem neg_3 : (-3 : Fin 6) = 3 := by decide
@[simp] private theorem neg_4 : (-4 : Fin 6) = 2 := by decide
@[simp] private theorem neg_5 : (-5 : Fin 6) = 1 := by decide

theorem permanent_matrix (w : Fin 6 → ℝ) : (matrix w).permanent = permanentPolynomial w := by
  simp (maxSteps := 4000000) only [MathAndTheory.GyiresCirculant5.permanent_succ,
    Fin.sum_univ_succ, Matrix.permanent_isEmpty, Matrix.submatrix_apply]
  norm_num (config := { maxSteps := 4000000 }) [matrix, permanentPolynomial, Equiv.swap_apply_def, Fin.ext_iff, Fin.succ,
    Fin.add_def, Fin.sub_def, Fin.neg_def]
  simp only [neg_1, neg_2, neg_3, neg_4, neg_5]
  ring
end MathAndTheory.Gyires.CirculantSix
