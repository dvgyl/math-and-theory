import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
An unbounded family for the three-projection Loewner arithmetic--geometric
mean comparison.  All conclusions use Mathlib's PosSemidef predicate. The matrices are
normalized rank-one outer products of explicit three-dimensional vectors.
-/

namespace ProjectionFamily

open Matrix

noncomputable section

abbrev Mat := Matrix (Fin 3) (Fin 3) ℝ
abbrev Vec := Fin 3 → ℝ

def IsOrthogonalProjection (P : Mat) : Prop := Pᵀ = P ∧ P * P = P

def arithmetic (X Y Z : Mat) : Mat := (1 / 3 : ℝ) • (X + Y + Z)

def geometric (X Y Z : Mat) : Mat :=
  (1 / 6 : ℝ) •
    (X * Y * Z + X * Z * Y + Y * X * Z + Y * Z * X + Z * X * Y + Z * Y * X)

def w : Vec := ![1, 1, 1]
def D (r : ℝ) : ℝ := 1 + 2 * r ^ 2
def v (r : ℝ) (i : Fin 3) : Vec :=
  ![![1 + 2 * r, 1 - r, 1 - r],
    ![1 - r, 1 + 2 * r, 1 - r],
    ![1 - r, 1 - r, 1 + 2 * r]] i

def proj (r : ℝ) (i : Fin 3) : Mat :=
  (3 * D r)⁻¹ • vecMulVec (v r i) (v r i)

theorem D_pos (r : ℝ) : 0 < D r := by
  dsimp [D]
  positivity

theorem D_ne (r : ℝ) : D r ≠ 0 := ne_of_gt (D_pos r)

theorem v_norm (r : ℝ) (i : Fin 3) :
    dotProduct (v r i) (v r i) = 3 * D r := by
  fin_cases i <;> simp [v, D, dotProduct, Fin.sum_univ_succ] <;> ring

theorem v_dot_w (r : ℝ) (i : Fin 3) : dotProduct (v r i) w = 3 := by
  fin_cases i <;> simp [v, w, dotProduct, Fin.sum_univ_succ] <;> ring

theorem v_dot_other (r : ℝ) (i j : Fin 3) (h : i ≠ j) :
    dotProduct (v r i) (v r j) = 3 * (1 - r ^ 2) := by
  fin_cases i <;> fin_cases j <;>
    simp_all [v, dotProduct, Fin.sum_univ_succ] <;> ring

theorem v_sum (r : ℝ) : v r 0 + v r 1 + v r 2 = (3 : ℝ) • w := by
  ext i
  fin_cases i <;> simp [v, w] <;> ring

theorem outer_square (u : Vec) :
    vecMulVec u u * vecMulVec u u = dotProduct u u • vecMulVec u u := by
  ext i j
  simp only [Matrix.mul_apply, vecMulVec_apply, Matrix.smul_apply, smul_eq_mul,
    dotProduct]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem proj_projection (r : ℝ) (i : Fin 3) : IsOrthogonalProjection (proj r i) := by
  constructor
  · ext j k
    simp [proj, vecMulVec_apply, mul_comm]
  · unfold proj
    rw [smul_mul, Matrix.mul_smul, outer_square, v_norm]
    simp only [smul_smul]
    congr 1
    field_simp [D_ne r]

theorem outer_mulVec (u z : Vec) :
    vecMulVec u u *ᵥ z = dotProduct u z • u := by
  ext i
  simp only [Matrix.mulVec, vecMulVec_apply, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem proj_mulVec (r : ℝ) (i : Fin 3) (z : Vec) :
    proj r i *ᵥ z = ((3 * D r)⁻¹ * dotProduct (v r i) z) • v r i := by
  rw [proj, smul_mulVec_assoc, outer_mulVec, smul_smul]

theorem proj_mulVec_w (r : ℝ) (i : Fin 3) :
    proj r i *ᵥ w = (D r)⁻¹ • v r i := by
  rw [proj_mulVec, v_dot_w]
  congr 1
  field_simp [D_ne r]

theorem proj_mulVec_other (r : ℝ) (i j : Fin 3) (h : i ≠ j) :
    proj r i *ᵥ v r j = ((1 - r ^ 2) / D r) • v r i := by
  rw [proj_mulVec, v_dot_other r i j h]
  congr 1
  field_simp [D_ne r]; ring

theorem arithmetic_w (r : ℝ) :
    arithmetic (proj r 0) (proj r 1) (proj r 2) *ᵥ w = (D r)⁻¹ • w := by
  simp only [arithmetic, smul_mulVec_assoc, add_mulVec, proj_mulVec_w]
  rw [← smul_add, ← smul_add, v_sum]
  simp only [smul_smul]
  congr 1
  ring

theorem geometric_w (r : ℝ) :
    geometric (proj r 0) (proj r 1) (proj r 2) *ᵥ w =
      ((1 - r ^ 2) ^ 2 / (D r) ^ 3) • w := by
  simp only [geometric, smul_mulVec_assoc, add_mulVec, ← mulVec_mulVec,
    proj_mulVec_w, mulVec_smul]
  simp [proj_mulVec_other, Matrix.mulVec_smul, smul_smul]
  ext i
  fin_cases i <;> simp [v, w] <;> field_simp [D_ne r] <;> ring

theorem arithmetic_cube_w (r : ℝ) :
    (arithmetic (proj r 0) (proj r 1) (proj r 2)) ^ 3 *ᵥ w =
      ((D r) ^ 3)⁻¹ • w := by
  simp only [pow_succ, pow_zero, one_mul, ← mulVec_mulVec,
    arithmetic_w, mulVec_smul, smul_smul]
  congr 1
  field_simp [D_ne r]; ring

theorem exact_quadratic_form (r C : ℝ) :
    dotProduct (star w)
      ((C • (arithmetic (proj r 0) (proj r 1) (proj r 2)) ^ 3 -
        geometric (proj r 0) (proj r 1) (proj r 2)) *ᵥ w) =
      3 * (C - (1 - r ^ 2) ^ 2) / (D r) ^ 3 := by
  rw [sub_mulVec, smul_mulVec_assoc, arithmetic_cube_w, geometric_w]
  simp only [dotProduct_sub, dotProduct_smul, smul_smul]
  norm_num [w, dotProduct, Fin.sum_univ_succ]
  ring

theorem ratio_exceeds (C : ℝ) : C < (1 - (|C| + 2) ^ 2) ^ 2 := by
  have ha : 0 ≤ |C| := abs_nonneg C
  have hc : C ≤ |C| := le_abs_self C
  have hlarge : |C| < (|C| + 2) ^ 2 - 1 := by nlinarith [sq_nonneg |C|]
  have hone : 1 ≤ (|C| + 2) ^ 2 - 1 := by nlinarith [sq_nonneg |C|]
  have hsquare : (|C| + 2) ^ 2 - 1 ≤ ((|C| + 2) ^ 2 - 1) ^ 2 := by
    nlinarith [sq_nonneg ((|C| + 2) ^ 2 - 2)]
  nlinarith

/-- No finite multiplicative constant repairs the Loewner comparison,
already for three real orthogonal projections on a three-dimensional space. -/
theorem no_finite_loewner_constant (C : ℝ) :
    ∃ X Y Z : Mat,
      IsOrthogonalProjection X ∧ IsOrthogonalProjection Y ∧
      IsOrthogonalProjection Z ∧
      ¬ (C • (arithmetic X Y Z) ^ 3 - geometric X Y Z).PosSemidef := by
  let r : ℝ := |C| + 2
  refine ⟨proj r 0, proj r 1, proj r 2, proj_projection r 0,
    proj_projection r 1, proj_projection r 2, ?_⟩
  intro h
  have hn := h.2 w
  rw [exact_quadratic_form] at hn
  have hC : C < (1 - r ^ 2) ^ 2 := ratio_exceeds C
  have hden : 0 < (D r) ^ 3 := pow_pos (D_pos r) 3
  have hnum : 3 * (C - (1 - r ^ 2) ^ 2) < 0 := by linarith
  have hneg := div_neg_of_neg_of_pos hnum hden
  linarith

#print axioms no_finite_loewner_constant

end

end ProjectionFamily
