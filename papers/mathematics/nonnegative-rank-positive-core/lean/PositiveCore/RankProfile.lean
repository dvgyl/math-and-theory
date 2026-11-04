module

public import PositiveCore.Compression
public import PositiveCore.KroneckerRank

@[expose] public section

namespace PositiveCore

open Matrix MatCKronecker
open scoped Kronecker

variable {m n s t : Type*} [Fintype m] [Fintype n] [Fintype s] [Fintype t]

/-- A nonnegative factorization of arbitrary finite width whose two ordinary
factor ranks are at most `r`.  This imposes no bound on the latent width. -/
def HasFactorRankBound (A : Matrix m n ℝ) (r : ℕ) : Prop :=
  ∃ k : ℕ, ∃ U : Matrix m (Fin k) ℝ, ∃ V : Matrix (Fin k) n ℝ,
    EntryNonneg U ∧ EntryNonneg V ∧ U * V = A ∧ U.rank ≤ r ∧ V.rank ≤ r

/-- The minimum, over all nonnegative factorizations and all finite widths,
of the maximum of the two ordinary factor ranks.  It is totalized to zero
when no nonnegative factorization exists. -/
noncomputable def factorRankProfile (A : Matrix m n ℝ) : ℕ := by
  classical
  exact if h : ∃ r, HasFactorRankBound A r then Nat.find h else 0

/-- The unavoidable excess in the larger ordinary factor rank. -/
noncomputable def factorRankDefect (A : Matrix m n ℝ) : ℕ :=
  factorRankProfile A - A.rank

theorem exists_hasFactorRankBound {A : Matrix m n ℝ} (hA : EntryNonneg A) :
    ∃ r, HasFactorRankBound A r := by
  obtain ⟨k, U, V, hU, hV, hUV⟩ := exists_hasNMF hA
  exact ⟨max U.rank V.rank, k, U, V, hU, hV, hUV,
    le_max_left _ _, le_max_right _ _⟩

theorem factorRankProfile_le_of_bound {A : Matrix m n ℝ} {r : ℕ}
    (h : HasFactorRankBound A r) : factorRankProfile A ≤ r := by
  classical
  rw [factorRankProfile, dite_eq_left ⟨r, h⟩]
  exact Nat.find_min' ⟨r, h⟩ h

theorem hasFactorRankBound_profile {A : Matrix m n ℝ} (hA : EntryNonneg A) :
    HasFactorRankBound A (factorRankProfile A) := by
  classical
  rw [factorRankProfile, dite_eq_left (exists_hasFactorRankBound hA)]
  exact Nat.find_spec (exists_hasFactorRankBound hA)

/-- The minimum in the definition is attained as the actual maximum of
the two factor ranks, not merely as an upper bound on them. -/
theorem exists_factorization_max_rank_eq_profile {A : Matrix m n ℝ}
    (hA : EntryNonneg A) :
    ∃ k : ℕ, ∃ U : Matrix m (Fin k) ℝ, ∃ V : Matrix (Fin k) n ℝ,
      EntryNonneg U ∧ EntryNonneg V ∧ U * V = A ∧
      max U.rank V.rank = factorRankProfile A := by
  obtain ⟨k, U, V, hU, hV, hUV, hUr, hVr⟩ := hasFactorRankBound_profile hA
  refine ⟨k, U, V, hU, hV, hUV, le_antisymm (max_le hUr hVr) ?_⟩
  exact factorRankProfile_le_of_bound
    ⟨k, U, V, hU, hV, hUV, le_max_left _ _, le_max_right _ _⟩

theorem rank_le_factorRankProfile {A : Matrix m n ℝ} (hA : EntryNonneg A) :
    A.rank ≤ factorRankProfile A := by
  obtain ⟨k, U, V, _, _, hUV, hUr, _⟩ := hasFactorRankBound_profile hA
  have h := Matrix.rank_mul_le_left U V
  rw [hUV] at h
  exact h.trans hUr

theorem factorRankProfile_le_nnrank {A : Matrix m n ℝ} (hA : EntryNonneg A) :
    factorRankProfile A ≤ nnrank A := by
  obtain ⟨U, V, hU, hV, hUV⟩ := hasNMF_nnrank hA
  apply factorRankProfile_le_of_bound
  refine ⟨nnrank A, U, V, hU, hV, hUV, ?_, ?_⟩
  · simpa using Matrix.rank_le_card_width U
  · simpa using Matrix.rank_le_card_height V

/-- Vanishing defect is exactly the existence of a factorization with both
ordinary factor ranks equal to the rank of the product. -/
theorem factorRankDefect_eq_zero_iff {A : Matrix m n ℝ} (hA : EntryNonneg A) :
    factorRankDefect A = 0 ↔
      ∃ k : ℕ, ∃ U : Matrix m (Fin k) ℝ, ∃ V : Matrix (Fin k) n ℝ,
        EntryNonneg U ∧ EntryNonneg V ∧ U * V = A ∧
        U.rank = A.rank ∧ V.rank = A.rank := by
  have hlow := rank_le_factorRankProfile hA
  constructor
  · intro hzero
    have hp : factorRankProfile A = A.rank := by
      unfold factorRankDefect at hzero
      omega
    obtain ⟨k, U, V, hU, hV, hUV, hUr, hVr⟩ := hasFactorRankBound_profile hA
    have hu := Matrix.rank_mul_le_left U V
    have hv := Matrix.rank_mul_le_right U V
    rw [hUV] at hu hv
    refine ⟨k, U, V, hU, hV, hUV, ?_, ?_⟩ <;> omega
  · rintro ⟨k, U, V, hU, hV, hUV, hUr, hVr⟩
    have hp : factorRankProfile A ≤ A.rank :=
      factorRankProfile_le_of_bound ⟨k, U, V, hU, hV, hUV, hUr.le, hVr.le⟩
    unfold factorRankDefect
    omega

/-- Quantitative compression bounds the minimum possible ordinary factor
ranks of `A` by the width excess in any NMF of `A ⊗ B`. -/
theorem factorRankProfile_add_product_rank_le_of_hasNMF
    (A : Matrix m n ℝ) (B : Matrix s t ℝ) {k : ℕ}
    (h : HasNMF (A ⊗ₖ B) k) (a : s) (b : t) (hab : 0 < B a b) :
    factorRankProfile A + (A ⊗ₖ B).rank ≤ A.rank + k := by
  obtain ⟨U, V, hU, hV, hUV, hUr, hVr⟩ :=
    hasNMF_kronecker_compression A B h a b hab
  have hp : factorRankProfile A ≤ max U.rank V.rank :=
    factorRankProfile_le_of_bound
      ⟨k, U, V, hU, hV, hUV, le_max_left _ _, le_max_right _ _⟩
  rcases le_total U.rank V.rank with hmax | hmax
  · rw [max_eq_right hmax] at hp
    omega
  · rw [max_eq_left hmax] at hp
    omega

theorem exists_positive_entry_of_nonzero {A : Matrix m n ℝ}
    (hA : EntryNonneg A) (hne : A ≠ 0) : ∃ i j, 0 < A i j := by
  by_contra! h
  apply hne
  ext i j
  exact le_antisymm (h i j) (hA i j)

/-- One-sided form of the factor-rank defect lower bound. -/
theorem factorRankProfile_add_product_rank_le_nnrank
    (A : Matrix m n ℝ) (B : Matrix s t ℝ)
    (hA : EntryNonneg A) (hB : EntryNonneg B) (hBne : B ≠ 0) :
    factorRankProfile A + (A ⊗ₖ B).rank ≤ A.rank + nnrank (A ⊗ₖ B) := by
  obtain ⟨a, b, hab⟩ := exists_positive_entry_of_nonzero hB hBne
  exact factorRankProfile_add_product_rank_le_of_hasNMF A B
    (hasNMF_nnrank (hA.kronecker hB)) a b hab

/-- Swapping Kronecker factors is a row and column permutation, preserving
both ordinary and nonnegative ranks. -/
theorem kronecker_swap_ranks (A : Matrix m n ℝ) (B : Matrix s t ℝ)
    (hA : EntryNonneg A) (hB : EntryNonneg B) :
    (B ⊗ₖ A).rank = (A ⊗ₖ B).rank ∧
      nnrank (B ⊗ₖ A) = nnrank (A ⊗ₖ B) := by
  classical
  have heq : (A ⊗ₖ B).submatrix (Equiv.prodComm s m) (Equiv.prodComm t n) =
      B ⊗ₖ A := by
    ext i j
    simp [Matrix.submatrix_apply, Matrix.kronecker_apply, mul_comm]
  constructor
  · rw [← heq]
    exact Matrix.rank_submatrix _ _ _
  · rw [← heq]
    exact nnrank_submatrix_equiv (hA.kronecker hB) _ _

theorem factorRankProfile_add_product_rank_le_nnrank_right
    (A : Matrix m n ℝ) (B : Matrix s t ℝ)
    (hA : EntryNonneg A) (hB : EntryNonneg B) (hAne : A ≠ 0) :
    factorRankProfile B + (A ⊗ₖ B).rank ≤ B.rank + nnrank (A ⊗ₖ B) := by
  have h := factorRankProfile_add_product_rank_le_nnrank B A hB hA hAne
  obtain ⟨hr, hnr⟩ := kronecker_swap_ranks A B hA hB
  simpa only [hr, hnr] using h

/-- Every nonzero tensor partner leaves at least the larger intrinsic
factor-rank defect above the ordinary rank of the product.  This is stated
with the actual ordinary product rank, so it is independent of any separate
formal theorem computing ranks of Kronecker products. -/
theorem rank_add_max_factorRankDefect_le_nnrank_kronecker
    (A : Matrix m n ℝ) (B : Matrix s t ℝ)
    (hA : EntryNonneg A) (hB : EntryNonneg B)
    (hAne : A ≠ 0) (hBne : B ≠ 0) :
    (A ⊗ₖ B).rank + max (factorRankDefect A) (factorRankDefect B) ≤
      nnrank (A ⊗ₖ B) := by
  have hleft := factorRankProfile_add_product_rank_le_nnrank A B hA hB hBne
  have hright := factorRankProfile_add_product_rank_le_nnrank_right A B hA hB hAne
  have hAlow := rank_le_factorRankProfile hA
  have hBlow := rank_le_factorRankProfile hB
  have hdA : (A ⊗ₖ B).rank + factorRankDefect A ≤ nnrank (A ⊗ₖ B) := by
    unfold factorRankDefect
    omega
  have hdB : (A ⊗ₖ B).rank + factorRankDefect B ≤ nnrank (A ⊗ₖ B) := by
    unfold factorRankDefect
    omega
  rcases le_total (factorRankDefect A) (factorRankDefect B) with h | h
  · simpa only [max_eq_right h] using hdB
  · simpa only [max_eq_left h] using hdA

/-- The same lower bound with the ordinary product rank evaluated. -/
theorem rank_mul_add_max_factorRankDefect_le_nnrank_kronecker
    (A : Matrix m n ℝ) (B : Matrix s t ℝ)
    (hA : EntryNonneg A) (hB : EntryNonneg B)
    (hAne : A ≠ 0) (hBne : B ≠ 0) :
    A.rank * B.rank + max (factorRankDefect A) (factorRankDefect B) ≤
      nnrank (A ⊗ₖ B) := by
  simpa only [rank_kronecker] using
    rank_add_max_factorRankDefect_le_nnrank_kronecker A B hA hB hAne hBne

end PositiveCore
