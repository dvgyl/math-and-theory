import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-!
An explicit obstruction to the three-projection Loewner arithmetic--geometric
mean comparison, motivated by Sun--Luo--Ye (2020).

All matrices below are over the real numbers. The geometric expression is
the average of all six products of three distinct projections. The conclusion
uses Mathlib's positive-semidefinite predicate, not entrywise matrix order.
-/

namespace ProjectionCounterexample

noncomputable section

open Matrix

abbrev Mat := Matrix (Fin 3) (Fin 3) ℝ

def IsOrthogonalProjection (P : Mat) : Prop := Pᵀ = P ∧ P * P = P

def P : Mat := (1 / 3 : ℝ) • !![1, -1, -1; -1, 1, 1; -1, 1, 1]
def Q : Mat := (1 / 3 : ℝ) • !![1, -1, 1; -1, 1, -1; 1, -1, 1]
def R : Mat := (1 / 3 : ℝ) • !![1, 1, -1; 1, 1, -1; -1, -1, 1]

def arithmetic (X Y Z : Mat) : Mat := (1 / 3 : ℝ) • (X + Y + Z)

def geometric (X Y Z : Mat) : Mat :=
  (1 / 6 : ℝ) •
    (X * Y * Z + X * Z * Y + Y * X * Z + Y * Z * X + Z * X * Y + Z * Y * X)

def w : Fin 3 → ℝ := ![1, 1, 1]

theorem P_projection : IsOrthogonalProjection P := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [P, Matrix.mul_apply, Fin.sum_univ_succ]

theorem Q_projection : IsOrthogonalProjection Q := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [Q, Matrix.mul_apply, Fin.sum_univ_succ]

theorem R_projection : IsOrthogonalProjection R := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [R, Matrix.mul_apply, Fin.sum_univ_succ]

theorem exact_quadratic_form :
    dotProduct (star w) (((arithmetic P Q R) ^ 3 - geometric P Q R) *ᵥ w) =
      -(8 / 243 : ℝ) := by
  norm_num [arithmetic, geometric, P, Q, R, w, pow_succ, Matrix.mul_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem not_positive_semidefinite :
    ¬ ((arithmetic P Q R) ^ 3 - geometric P Q R).PosSemidef := by
  intro h
  have hn := h.2 w
  rw [exact_quadratic_form] at hn
  norm_num at hn

/-- The three-projection Loewner arithmetic--geometric mean comparison fails. -/
theorem three_projection_counterexample :
    ∃ X Y Z : Mat,
      IsOrthogonalProjection X ∧ IsOrthogonalProjection Y ∧
      IsOrthogonalProjection Z ∧
      ¬ ((arithmetic X Y Z) ^ 3 - geometric X Y Z).PosSemidef := by
  exact ⟨P, Q, R, P_projection, Q_projection, R_projection, not_positive_semidefinite⟩

#print axioms three_projection_counterexample

end

end ProjectionCounterexample
