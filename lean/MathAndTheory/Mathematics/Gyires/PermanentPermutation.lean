module

public import MathAndTheory.Mathematics.Gyires.CirculantFive.Remarks

@[expose] public section

namespace MathAndTheory.Gyires

variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped BigOperators

/-- Independent row and column permutations preserve the permanent. -/
theorem permanent_submatrix_perm (A : Matrix n n ℝ) (σ τ : Equiv.Perm n) :
    (A.submatrix σ τ).permanent = A.permanent := by
  calc
    (A.submatrix σ τ).permanent = ((A.submatrix σ id).submatrix id τ).permanent := rfl
    _ = (A.submatrix σ id).permanent := Matrix.permanent_permute_rows τ _
    _ = A.permanent := Matrix.permanent_permute_cols σ _

omit [DecidableEq n] in
/-- A row Gram matrix changes by the same permutation on both indices. -/
theorem submatrix_perm_mul_transpose (A : Matrix n n ℝ) (σ τ : Equiv.Perm n) :
    A.submatrix σ τ * (A.submatrix σ τ).transpose =
      (A * A.transpose).submatrix σ σ := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp τ (fun k => A (σ i) k * A (σ j) k)

omit [DecidableEq n] in
/-- A column Gram matrix changes by the same permutation on both indices. -/
theorem transpose_mul_submatrix_perm (A : Matrix n n ℝ) (σ τ : Equiv.Perm n) :
    (A.submatrix σ τ).transpose * A.submatrix σ τ =
      (A.transpose * A).submatrix τ τ := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp σ (fun k => A k (τ i) * A k (τ j))

/-- Both strong Gram bounds are invariant under independent row and column permutations. -/
theorem strong_bounds_submatrix_perm_iff (A : Matrix n n ℝ) (σ τ : Equiv.Perm n) (K : ℝ) :
    (K * (A.submatrix σ τ * (A.submatrix σ τ).transpose).permanent ≤
        (A.submatrix σ τ).permanent ^ 2 ∧
      K * ((A.submatrix σ τ).transpose * A.submatrix σ τ).permanent ≤
        (A.submatrix σ τ).permanent ^ 2) ↔
      (K * (A * A.transpose).permanent ≤ A.permanent ^ 2 ∧
        K * (A.transpose * A).permanent ≤ A.permanent ^ 2) := by
  rw [submatrix_perm_mul_transpose, transpose_mul_submatrix_perm]
  simp only [permanent_submatrix_perm]

/-- Permuted matrices satisfy Gyires's bound whenever the original matrix has both strong bounds. -/
theorem gyires_submatrix_perm_of_strong (A : Matrix n n ℝ) (σ τ : Equiv.Perm n)
    (K : ℝ) (hK : 0 ≤ K)
    (hleft : K * (A * A.transpose).permanent ≤ A.permanent ^ 2)
    (hright : K * (A.transpose * A).permanent ≤ A.permanent ^ 2) :
    K * ((A.submatrix σ τ * (A.submatrix σ τ).transpose).permanent +
      ((A.submatrix σ τ).transpose * A.submatrix σ τ).permanent +
      2 * (A.submatrix σ τ * A.submatrix σ τ).permanent) ≤
        4 * (A.submatrix σ τ).permanent ^ 2 := by
  obtain ⟨hleft', hright'⟩ := (strong_bounds_submatrix_perm_iff A σ τ K).2 ⟨hleft, hright⟩
  exact MathAndTheory.GyiresCirculant5.gyires_of_strong (A.submatrix σ τ) K hK hleft' hright'

end MathAndTheory.Gyires
