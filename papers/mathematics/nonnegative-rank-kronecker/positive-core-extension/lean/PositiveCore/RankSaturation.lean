module

public import MatCKronecker.BasicFactorizations

@[expose] public section

namespace PositiveCore

open Matrix Module

variable {m n k l t : Type*} [Fintype m] [Fintype n] [Fintype k] [DecidableEq k]

/-- A matrix of full row rank has an exact real right inverse. -/
theorem exists_right_inverse_of_full_row_rank (H : Matrix k n ℝ)
    (hH : H.rank = Fintype.card k) :
    ∃ J : Matrix n k ℝ, H * J = 1 := by
  classical
  have hrange : LinearMap.range H.mulVecLin = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by simpa only [Matrix.rank, finrank_pi] using hH)
  obtain ⟨j, hj⟩ := H.mulVecLin.exists_rightInverse_of_surjective hrange
  refine ⟨LinearMap.toMatrix' j, ?_⟩
  apply Matrix.toLin'.injective
  change (H * LinearMap.toMatrix' j).mulVecLin = (1 : Matrix k k ℝ).mulVecLin
  rw [Matrix.mulVecLin_mul, Matrix.mulVecLin_one]
  change H.mulVecLin.comp (Matrix.toLin' (LinearMap.toMatrix' j)) = LinearMap.id
  rw [Matrix.toLin'_toMatrix']
  exact hj

/-- A matrix of full column rank has an exact real left inverse. -/
theorem exists_left_inverse_of_full_column_rank (L : Matrix m k ℝ)
    (hL : L.rank = Fintype.card k) :
    ∃ J : Matrix k m ℝ, J * L = 1 := by
  classical
  have hdim := L.mulVecLin.finrank_range_add_finrank_ker
  have hkerdim : finrank ℝ (LinearMap.ker L.mulVecLin) = 0 := by
    change L.rank + finrank ℝ (LinearMap.ker L.mulVecLin) = finrank ℝ (k → ℝ) at hdim
    rw [hL, finrank_pi] at hdim
    omega
  have hker : LinearMap.ker L.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp hkerdim
  obtain ⟨j, hj⟩ := L.mulVecLin.exists_leftInverse_of_injective hker
  refine ⟨LinearMap.toMatrix' j, ?_⟩
  apply Matrix.toLin'.injective
  change (LinearMap.toMatrix' j * L).mulVecLin = (1 : Matrix k k ℝ).mulVecLin
  rw [Matrix.mulVecLin_mul, Matrix.mulVecLin_one]
  change (Matrix.toLin' (LinearMap.toMatrix' j)).comp L.mulVecLin = LinearMap.id
  rw [Matrix.toLin'_toMatrix']
  exact hj

/-- If a factorization width equals ordinary rank, both factor maps have their
maximal possible rank. -/
theorem saturated_factor_ranks (L : Matrix m k ℝ) (H : Matrix k n ℝ)
    (h : (L * H).rank = Fintype.card k) :
    L.rank = Fintype.card k ∧ H.rank = Fintype.card k := by
  have hL := Matrix.rank_mul_le_left L H
  have hH := Matrix.rank_mul_le_right L H
  have hbL := L.rank_le_card_width
  have hbH := H.rank_le_card_height
  omega

/-- Every left annihilator of a saturated product already annihilates its left
factor.  No positivity hypothesis is needed for this linear-algebraic fact. -/
theorem left_annihilator_transfer (L : Matrix m k ℝ) (H : Matrix k n ℝ)
    (h : (L * H).rank = Fintype.card k)
    (C : Matrix l m ℝ) (hC : C * (L * H) = 0) : C * L = 0 := by
  classical
  obtain ⟨J, hJ⟩ := exists_right_inverse_of_full_row_rank H
    (saturated_factor_ranks L H h).2
  calc
    C * L = (C * L) * (H * J) := by rw [hJ, Matrix.mul_one]
    _ = (C * (L * H)) * J := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hC, Matrix.zero_mul]

/-- The corresponding right-annihilator transfer. -/
theorem right_annihilator_transfer (L : Matrix m k ℝ) (H : Matrix k n ℝ)
    (h : (L * H).rank = Fintype.card k)
    (C : Matrix n t ℝ) (hC : (L * H) * C = 0) : H * C = 0 := by
  classical
  obtain ⟨J, hJ⟩ := exists_left_inverse_of_full_column_rank L
    (saturated_factor_ranks L H h).1
  calc
    H * C = (J * L) * (H * C) := by rw [hJ, Matrix.one_mul]
    _ = J * ((L * H) * C) := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hC, Matrix.mul_zero]

end PositiveCore
