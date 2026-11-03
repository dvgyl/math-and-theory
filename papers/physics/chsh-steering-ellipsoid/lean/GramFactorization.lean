import ObeseSharp
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases

set_option autoImplicit false

namespace ObeseSharp
noncomputable section

/-- A symmetric representative of the three-dimensional Gram matrix.
The sign of its single off-diagonal entry does not change its spectrum. -/
def gram (c u z : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![xx c z, 0, Real.sqrt (offSq c u z);
     0, q c u z, 0;
     Real.sqrt (offSq c u z), 0, zz c u z]

theorem offSq_nonneg (c u z : ℝ) (hc : c ≤ 1) (hu : 0 ≤ u) :
    0 ≤ offSq c u z := by
  unfold offSq
  have hp : 0 ≤ 1 - c := by linarith
  positivity

theorem gram_symmetric (c u z : ℝ) : (gram c u z).transpose = gram c u z := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Direct determinant calculation from the concrete 3 by 3 matrix. -/
theorem gram_characteristic_factorization (c u z t : ℝ)
    (hc : c ≤ 1) (hu : 0 ≤ u) :
    Matrix.det (t • (1 : Matrix (Fin 3) (Fin 3) ℝ) - gram c u z) =
      (t - q c u z) *
        (t ^ 2 - trace c u z * t + xx c z * zz c u z - offSq c u z) := by
  have hs := Real.sq_sqrt (offSq_nonneg c u z hc hu)
  rw [Matrix.det_fin_three]
  norm_num [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, gram,
    Matrix.of_apply]
  dsimp [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail]
  norm_num
  unfold trace
  have he : (t - xx c z) * (t - q c u z) * (t - zz c u z) -
      Real.sqrt (offSq c u z) * (t - q c u z) * Real.sqrt (offSq c u z) =
      (t - q c u z) * (t ^ 2 - (xx c z + zz c u z) * t +
        xx c z * zz c u z - Real.sqrt (offSq c u z) ^ 2) := by ring
  rw [hs] at he
  nlinarith

/-- Sum and product specify both roots exactly. -/
theorem block_root_sum_product (c u z : ℝ) (hc : c ≤ 1) (hu : 0 ≤ u) :
    lower c u z + upper c u z = trace c u z ∧
    lower c u z * upper c u z = xx c z * zz c u z - offSq c u z := by
  have hs := Real.sq_sqrt (discr_nonneg c u z hc hu)
  have hd : discr c u z =
      trace c u z ^ 2 - 4 * (xx c z * zz c u z - offSq c u z) := by
    unfold discr trace
    ring
  unfold lower upper
  constructor <;> nlinarith

/-- The three ordered roots come from the actual concrete Gram matrix. -/
theorem gram_three_roots (c u z t : ℝ) (hc : c ≤ 1) (hu : 0 ≤ u) :
    Matrix.det (t • (1 : Matrix (Fin 3) (Fin 3) ℝ) - gram c u z) =
      (t - q c u z) * (t - lower c u z) * (t - upper c u z) := by
  rw [gram_characteristic_factorization c u z t hc hu]
  rcases block_root_sum_product c u z hc hu with ⟨hs, hp⟩
  calc
    (t - q c u z) *
        (t ^ 2 - trace c u z * t + xx c z * zz c u z - offSq c u z) =
      (t - q c u z) *
        (t ^ 2 - (lower c u z + upper c u z) * t + lower c u z * upper c u z) := by
          rw [hs, hp]
          ring
    _ = _ := by ring

/-- There are no additional characteristic roots. -/
theorem gram_root_iff (c u z t : ℝ) (hc : c ≤ 1) (hu : 0 ≤ u) :
    Matrix.det (t • (1 : Matrix (Fin 3) (Fin 3) ℝ) - gram c u z) = 0 ↔
      t = q c u z ∨ t = lower c u z ∨ t = upper c u z := by
  rw [gram_three_roots c u z t hc hu]
  simp only [mul_eq_zero, sub_eq_zero]
  tauto

end
end ObeseSharp
