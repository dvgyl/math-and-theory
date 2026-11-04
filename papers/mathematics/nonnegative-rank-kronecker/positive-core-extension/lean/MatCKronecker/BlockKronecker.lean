module

public import MatCKronecker.BlockSum
public import MatCKronecker.BasicFactorizations

@[expose] public section

namespace MatCKronecker

open Matrix
open scoped Kronecker

variable {m n p q r s u v : Type*}

/-- The explicit row/column permutation distributing two binary sums over a
Cartesian product. -/
def blockProductEquiv (m p r u : Type*) :
    (m ⊕ p) × (r ⊕ u) ≃ ((m × r) ⊕ (m × u)) ⊕ ((p × r) ⊕ (p × u)) :=
  (Equiv.sumProdDistrib m p (r ⊕ u)).trans
    ((Equiv.prodSumDistrib m r u).sumCongr (Equiv.prodSumDistrib p r u))

theorem blockDiag_kronecker_reindex
    (A : Matrix m n ℝ) (B : Matrix p q ℝ)
    (C : Matrix r s ℝ) (D : Matrix u v ℝ) :
    (Matrix.fromBlocks
      (Matrix.fromBlocks (A ⊗ₖ C) 0 0 (A ⊗ₖ D)) 0 0
      (Matrix.fromBlocks (B ⊗ₖ C) 0 0 (B ⊗ₖ D))).submatrix
        (blockProductEquiv m p r u) (blockProductEquiv n q s v) =
      (Matrix.fromBlocks A 0 0 B) ⊗ₖ (Matrix.fromBlocks C 0 0 D) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  cases i₁ <;> cases i₂ <;> cases j₁ <;> cases j₂ <;>
    simp [Matrix.submatrix_apply, blockProductEquiv]

theorem HasNMF.blockDiag_kronecker
    {A : Matrix m n ℝ} {B : Matrix p q ℝ}
    {C : Matrix r s ℝ} {D : Matrix u v ℝ} {a b c d : ℕ}
    (hAC : HasNMF (A ⊗ₖ C) a) (hAD : HasNMF (A ⊗ₖ D) b)
    (hBC : HasNMF (B ⊗ₖ C) c) (hBD : HasNMF (B ⊗ₖ D) d) :
    HasNMF ((Matrix.fromBlocks A 0 0 B) ⊗ₖ (Matrix.fromBlocks C 0 0 D))
      ((a + b) + (c + d)) := by
  have h := ((hAC.blockDiag hAD).blockDiag (hBC.blockDiag hBD)).submatrix
    (blockProductEquiv m p r u) (blockProductEquiv n q s v)
  simpa only [blockDiag_kronecker_reindex] using h

theorem HasNMF.kronecker_swap {A : Matrix m n ℝ} {B : Matrix p q ℝ} {k : ℕ}
    (h : HasNMF (A ⊗ₖ B) k) : HasNMF (B ⊗ₖ A) k := by
  have heq : (A ⊗ₖ B).submatrix (Equiv.prodComm p m) (Equiv.prodComm q n) = B ⊗ₖ A := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    simp [mul_comm]
  simpa only [heq] using h.submatrix (Equiv.prodComm p m) (Equiv.prodComm q n)

end MatCKronecker
