module

public import MatCKronecker.CrossFactors
public import MatCKronecker.PositiveIdentity

@[expose] public section

namespace PositiveCore

open Matrix MatCKronecker
open scoped Kronecker

/-- Ordinary rank of the original seed tensored with an arbitrary positive
diagonal perturbation of the all-ones matrix.  This supplies the exact lower
rank needed to settle the original mixed-block ambiguity. -/
theorem original_seed_tensor_rank {n : Type*} [Fintype n] [DecidableEq n]
    (ρ : ℝ) (hρ : 0 < ρ) :
    (seed ⊗ₖ nearOne n ρ).rank = 3 * Fintype.card n := by
  apply le_antisymm
  · have hfac :
        (seedRankLeft ⊗ₖ nearOne n ρ) *
          (seedRankRight ⊗ₖ (1 : Matrix n n ℝ)) = seed ⊗ₖ nearOne n ρ := by
      rw [← Matrix.mul_kronecker_mul, seed_rank_factorization, Matrix.mul_one]
    rw [← hfac]
    apply (Matrix.rank_mul_le_left _ _).trans
    simpa using (seedRankLeft ⊗ₖ nearOne n ρ).rank_le_card_width
  · have hdet : (nearOne n ρ).det ≠ 0 := by
      have he := congrArg Matrix.det (nearOneInverse_mul n hρ)
      rw [Matrix.det_mul, Matrix.det_one] at he
      intro hz
      rw [hz, mul_zero] at he
      norm_num at he
    have hminor : (seedMinor ⊗ₖ nearOne n ρ).det ≠ 0 := by
      rw [Matrix.det_kronecker, seedMinor_det]
      exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hdet)
    have hr : (seedMinor ⊗ₖ nearOne n ρ).rank = 3 * Fintype.card n := by
      simpa using Matrix.rank_of_det_ne_zero hminor
    let f : Fin 3 × n → Fin 4 × n := fun i => (i.1.castSucc, i.2)
    have he : seedMinor ⊗ₖ nearOne n ρ =
        (seed ⊗ₖ nearOne n ρ).submatrix f f := by rfl
    rw [← hr, he]
    exact Matrix.rank_submatrix_le _ f f

theorem original_mixed_rank {t : ℕ} (ht : 0 < t) :
    (seed ⊗ₖ smallBlock t).rank = 3 * (t + 1) := by
  simpa [smallBlock] using
    (original_seed_tensor_rank (n := Option (Fin t)) (crossEpsilon t) (crossEpsilon_pos ht))

end PositiveCore
