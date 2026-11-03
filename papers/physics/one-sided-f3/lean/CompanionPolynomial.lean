import SpectralBridge
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The companion determinant is the actual secular polynomial

The block determinant identity is proved for arbitrary real square matrices,
without an invertibility assumption.  In three diagonal spectral coordinates
it is exactly the explicit sextic used in the closed-form theorem.
-/

noncomputable section
open scoped BigOperators Matrix
namespace FilteredF3

section Block
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def blockRotation : Matrix (Sum ι ι) (Sum ι ι) ℝ :=
  Matrix.fromBlocks 0 1 (-1) 0

theorem det_blockRotation : (blockRotation (ι := ι)).det = 1 := by
  let U : Matrix (Sum ι ι) (Sum ι ι) ℝ := Matrix.fromBlocks 1 1 0 1
  let L : Matrix (Sum ι ι) (Sum ι ι) ℝ := Matrix.fromBlocks 1 0 (-1) 1
  have hfactor : blockRotation (ι := ι) = U * L * U := by
    simp [blockRotation, U, L, Matrix.fromBlocks_multiply]
  rw [hfactor, Matrix.det_mul, Matrix.det_mul]
  simp [U, L, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₁₂]

/-- The key block identity holds even at singular diagonal blocks. -/
theorem det_companion_block (A R : Matrix ι ι ℝ) :
    (Matrix.fromBlocks A (-1) (-R) A).det = (A * A - R).det := by
  let G : Matrix (Sum ι ι) (Sum ι ι) ℝ := Matrix.fromBlocks 1 (-A) 0 1
  have hG : G.det = 1 := by simp [G, Matrix.det_fromBlocks_zero₂₁]
  have hm : blockRotation (ι := ι) * Matrix.fromBlocks A (-1) (-R) A =
      Matrix.fromBlocks (-R) A (-A) 1 := by
    simp [blockRotation, Matrix.fromBlocks_multiply]
  have hGm : G * Matrix.fromBlocks (-R) A (-A) 1 =
      Matrix.fromBlocks (A * A - R) 0 (-A) 1 := by
    simp [G, Matrix.fromBlocks_multiply, sub_eq_add_neg, add_comm]
  calc
    (Matrix.fromBlocks A (-1) (-R) A).det =
        (blockRotation (ι := ι) * Matrix.fromBlocks A (-1) (-R) A).det := by
      rw [Matrix.det_mul, det_blockRotation, one_mul]
    _ = (G * (blockRotation (ι := ι) * Matrix.fromBlocks A (-1) (-R) A)).det := by
      simp only [Matrix.det_mul, hG, one_mul]
    _ = (A * A - R).det := by
      rw [hm, hGm, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one]

def companionMatrix (H : Matrix ι ι ℝ) (g : ι → ℝ) :
    Matrix (Sum ι ι) (Sum ι ι) ℝ :=
  Matrix.fromBlocks H 1 (Matrix.vecMulVec g g) H

theorem companion_shift_blocks (H : Matrix ι ι ℝ) (g : ι → ℝ) (z : ℝ) :
    z • (1 : Matrix (Sum ι ι) (Sum ι ι) ℝ) - companionMatrix H g =
      Matrix.fromBlocks (z • 1 - H) (-1) (-(Matrix.vecMulVec g g)) (z • 1 - H) := by
  ext i j
  cases i <;> cases j <;>
    simp [companionMatrix, Matrix.fromBlocks, Matrix.one_apply, Matrix.smul_apply]

/-- The characteristic determinant of the 2n companion matrix is the
rank-one perturbation of the squared shifted n-by-n matrix. -/
theorem companion_characteristic_determinant
    (H : Matrix ι ι ℝ) (g : ι → ℝ) (z : ℝ) :
    (z • (1 : Matrix (Sum ι ι) (Sum ι ι) ℝ) - companionMatrix H g).det =
      ((z • 1 - H) * (z • 1 - H) - Matrix.vecMulVec g g).det := by
  rw [companion_shift_blocks, det_companion_block]

end Block

/-- Direct determinant expansion supplies the exact secular sextic, including
all zero/repeated diagonal entries and singular evaluation points. -/
theorem diagonal_rank_one_determinant_three (h g : Fin 3 → ℝ) (z : ℝ) :
    (Matrix.diagonal (fun i => (z - h i)^2) - Matrix.vecMulVec g g).det =
      secularPolynomial h g z := by
  rw [three_dimensional_sextic]
  simp [Matrix.det_fin_three, Matrix.diagonal, Matrix.vecMulVec, Matrix.sub_apply]
  ring

/-- The stated polynomial really is the characteristic determinant of an
explicit six-by-six matrix, not a separately assumed root equation. -/
theorem companion_sextic_three (h g : Fin 3 → ℝ) (z : ℝ) :
    (z • (1 : Matrix (Sum (Fin 3) (Fin 3)) (Sum (Fin 3) (Fin 3)) ℝ) -
      companionMatrix (Matrix.diagonal h) g).det = secularPolynomial h g z := by
  rw [companion_characteristic_determinant]
  have hd : z • (1 : Matrix (Fin 3) (Fin 3) ℝ) - Matrix.diagonal h =
      Matrix.diagonal (fun i => z - h i) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.diagonal_apply, Matrix.one_apply]
    · simp [Matrix.diagonal_apply, Matrix.one_apply, hij]
  rw [hd, Matrix.diagonal_mul_diagonal]
  simpa [pow_two] using diagonal_rank_one_determinant_three h g z

end FilteredF3
