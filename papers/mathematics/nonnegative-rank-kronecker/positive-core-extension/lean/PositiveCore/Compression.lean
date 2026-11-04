module

public import MatCKronecker.BasicFactorizations

@[expose] public section

namespace PositiveCore

open Matrix MatCKronecker
open scoped BigOperators Kronecker

variable {m n s t κ : Type*}
  [Fintype m] [Fintype n] [Fintype s] [Fintype t] [Fintype κ]

/-- A fixed auxiliary row of a Kronecker product has rank at most the rank
of the first factor.  The proof gives an explicit matrix multiplying `A`. -/
theorem rank_kronecker_row_slice_le (A : Matrix m n ℝ) (B : Matrix s t ℝ)
    (a : s) :
    ((A ⊗ₖ B).submatrix (fun i => (i, a)) id).rank ≤ A.rank := by
  classical
  let R : Matrix n (n × t) ℝ := fun i j => if i = j.1 then B a j.2 else 0
  have heq : (A ⊗ₖ B).submatrix (fun i => (i, a)) id = A * R := by
    ext i j
    change A i j.1 * B a j.2 = (A * R) i j
    rw [Matrix.mul_apply]
    simp [R, mul_ite]
  rw [heq]
  exact Matrix.rank_mul_le_left _ _

/-- A fixed auxiliary column of a Kronecker product has rank at most the
rank of the first factor. -/
theorem rank_kronecker_col_slice_le (A : Matrix m n ℝ) (B : Matrix s t ℝ)
    (b : t) :
    ((A ⊗ₖ B).submatrix id (fun j => (j, b))).rank ≤ A.rank := by
  classical
  let S : Matrix (m × s) m ℝ := fun i j => if i.1 = j then B i.2 b else 0
  have heq : (A ⊗ₖ B).submatrix id (fun j => (j, b)) = S * A := by
    ext i j
    change A i.1 j * B i.2 b = (S * A) i j
    rw [Matrix.mul_apply]
    simp [S, ite_mul, mul_comm]
  rw [heq]
  exact Matrix.rank_mul_le_right _ _

/-- A nonzero entry in the selected auxiliary row makes the preceding rank
bound an equality, with no hypothesis on the signs of either matrix. -/
theorem rank_kronecker_row_slice (A : Matrix m n ℝ) (B : Matrix s t ℝ)
    (a : s) (b : t) (hab : B a b ≠ 0) :
    ((A ⊗ₖ B).submatrix (fun i => (i, a)) id).rank = A.rank := by
  classical
  apply le_antisymm (rank_kronecker_row_slice_le A B a)
  have hsub := Matrix.rank_submatrix_le
    ((A ⊗ₖ B).submatrix (fun i => (i, a)) id) id (fun j => (j, b))
  have heq : ((A ⊗ₖ B).submatrix (fun i => (i, a)) id).submatrix id
      (fun j => (j, b)) = B a b • A := by
    ext i j
    simp [Matrix.submatrix_apply, Matrix.kronecker_apply, mul_comm]
  rw [heq, Matrix.rank_smul_of_mem_nonZeroDivisors A
    (mem_nonZeroDivisors_of_ne_zero hab)] at hsub
  exact hsub

/-- The column version of `rank_kronecker_row_slice`. -/
theorem rank_kronecker_col_slice (A : Matrix m n ℝ) (B : Matrix s t ℝ)
    (a : s) (b : t) (hab : B a b ≠ 0) :
    ((A ⊗ₖ B).submatrix id (fun j => (j, b))).rank = A.rank := by
  classical
  apply le_antisymm (rank_kronecker_col_slice_le A B b)
  have hsub := Matrix.rank_submatrix_le
    ((A ⊗ₖ B).submatrix id (fun j => (j, b))) (fun i => (i, a)) id
  have heq : ((A ⊗ₖ B).submatrix id (fun j => (j, b))).submatrix
      (fun i => (i, a)) id = B a b • A := by
    ext i j
    simp [Matrix.submatrix_apply, Matrix.kronecker_apply, mul_comm]
  rw [heq, Matrix.rank_smul_of_mem_nonZeroDivisors A
    (mem_nonZeroDivisors_of_ne_zero hab)] at hsub
  exact hsub

/-- Every nonnegative factorization of a Kronecker product compresses to a
factorization of the first factor.  Each compressed factor's ordinary rank
can exceed the rank of `A` by at most the original factorization's width
minus the ordinary rank of the product.  The addition-only form avoids any
convention about subtraction on natural numbers. -/
theorem kronecker_factor_compression
    (A : Matrix m n ℝ) (B : Matrix s t ℝ)
    (L : Matrix (m × s) κ ℝ) (H : Matrix κ (n × t) ℝ)
    (hL : EntryNonneg L) (hH : EntryNonneg H) (hLH : L * H = A ⊗ₖ B)
    (a : s) (b : t) (hab : 0 < B a b) :
    ∃ U : Matrix m κ ℝ, ∃ V : Matrix κ n ℝ,
      EntryNonneg U ∧ EntryNonneg V ∧ U * V = A ∧
      U.rank + (A ⊗ₖ B).rank ≤ A.rank + Fintype.card κ ∧
      V.rank + (A ⊗ₖ B).rank ≤ A.rank + Fintype.card κ := by
  classical
  let U : Matrix m κ ℝ := L.submatrix (fun i => (i, a)) id
  let V₀ : Matrix κ n ℝ := H.submatrix id (fun j => (j, b))
  let V : Matrix κ n ℝ := (B a b)⁻¹ • V₀
  have hrow : U * H = (A ⊗ₖ B).submatrix (fun i => (i, a)) id := by
    ext i j
    simpa [U, Matrix.mul_apply] using congrArg (fun M => M (i, a) j) hLH
  have hcol : L * V₀ = (A ⊗ₖ B).submatrix id (fun j => (j, b)) := by
    ext i j
    simpa [V₀, Matrix.mul_apply] using congrArg (fun M => M i (j, b)) hLH
  have hUV₀ : U * V₀ = B a b • A := by
    ext i j
    simpa [U, V₀, Matrix.mul_apply, Matrix.kronecker_apply, mul_comm] using
      congrArg (fun M => M (i, a) (j, b)) hLH
  have hUV : U * V = A := by
    dsimp [V]
    rw [Matrix.mul_smul, hUV₀, smul_smul]
    simp [ne_of_gt hab]
  have hVr : V.rank = V₀.rank := by
    exact Matrix.rank_smul_of_mem_nonZeroDivisors V₀
      (mem_nonZeroDivisors_of_ne_zero (inv_ne_zero (ne_of_gt hab)))
  have hUr : U.rank + (A ⊗ₖ B).rank ≤ A.rank + Fintype.card κ := by
    have hSyl := Matrix.rank_mul_ge U H
    have hprod := Matrix.rank_mul_le_right L H
    rw [hLH] at hprod
    rw [hrow, rank_kronecker_row_slice A B a b (ne_of_gt hab)] at hSyl
    omega
  have hV₀r : V₀.rank + (A ⊗ₖ B).rank ≤ A.rank + Fintype.card κ := by
    have hSyl := Matrix.rank_mul_ge L V₀
    have hprod := Matrix.rank_mul_le_left L H
    rw [hLH] at hprod
    rw [hcol, rank_kronecker_col_slice A B a b (ne_of_gt hab)] at hSyl
    omega
  refine ⟨U, V, ?_, ?_, hUV, hUr, ?_⟩
  · intro i j
    exact hL (i, a) j
  · intro i j
    exact mul_nonneg (le_of_lt (inv_pos.mpr hab)) (hH i (j, b))
  · simpa [hVr] using hV₀r

/-- In particular, ordinary-rank saturation of a Kronecker product forces
the first factor to have a nonnegative factorization with both factor
ranks equal to its own rank. -/
theorem balanced_factorization_of_kronecker_rank_saturation
    (A : Matrix m n ℝ) (B : Matrix s t ℝ)
    (L : Matrix (m × s) κ ℝ) (H : Matrix κ (n × t) ℝ)
    (hL : EntryNonneg L) (hH : EntryNonneg H) (hLH : L * H = A ⊗ₖ B)
    (hwidth : Fintype.card κ = (A ⊗ₖ B).rank)
    (a : s) (b : t) (hab : 0 < B a b) :
    ∃ U : Matrix m κ ℝ, ∃ V : Matrix κ n ℝ,
      EntryNonneg U ∧ EntryNonneg V ∧ U * V = A ∧
      U.rank = A.rank ∧ V.rank = A.rank := by
  obtain ⟨U, V, hU, hV, hUV, hUr, hVr⟩ :=
    kronecker_factor_compression A B L H hL hH hLH a b hab
  have hlowU := Matrix.rank_mul_le_left U V
  have hlowV := Matrix.rank_mul_le_right U V
  rw [hUV] at hlowU hlowV
  refine ⟨U, V, hU, hV, hUV, ?_, ?_⟩ <;> omega

/-- The compression theorem for the repository's `HasNMF` predicate. -/
theorem hasNMF_kronecker_compression
    (A : Matrix m n ℝ) (B : Matrix s t ℝ) {k : ℕ}
    (h : HasNMF (A ⊗ₖ B) k) (a : s) (b : t) (hab : 0 < B a b) :
    ∃ U : Matrix m (Fin k) ℝ, ∃ V : Matrix (Fin k) n ℝ,
      EntryNonneg U ∧ EntryNonneg V ∧ U * V = A ∧
      U.rank + (A ⊗ₖ B).rank ≤ A.rank + k ∧
      V.rank + (A ⊗ₖ B).rank ≤ A.rank + k := by
  obtain ⟨L, H, hL, hH, hLH⟩ := h
  simpa only [Fintype.card_fin] using
    kronecker_factor_compression A B L H hL hH hLH a b hab

end PositiveCore
