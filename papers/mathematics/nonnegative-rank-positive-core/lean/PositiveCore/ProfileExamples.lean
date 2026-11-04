module

public import PositiveCore.TensorObstruction

@[expose] public section

namespace PositiveCore.ProfileExamples

open Matrix MatCKronecker
open scoped BigOperators

/-- Equality of the product rank and left factor rank makes their column
spaces equal, so every left annihilator descends to the factor. -/
theorem left_annihilator_of_equal_rank
    {m n k l : Type*} [Fintype m] [Fintype n] [Fintype k]
    (L : Matrix m k ℝ) (H : Matrix k n ℝ)
    (h : (L * H).rank = L.rank)
    (C : Matrix l m ℝ) (hC : C * (L * H) = 0) : C * L = 0 := by
  classical
  have hs : LinearMap.range (L * H).mulVecLin ≤ LinearMap.range L.mulVecLin := by
    rw [Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range H.mulVecLin L.mulVecLin
  have heq : LinearMap.range (L * H).mulVecLin = LinearMap.range L.mulVecLin :=
    Submodule.eq_of_le_of_finrank_eq hs h
  have hzero : C.mulVecLin.comp (L * H).mulVecLin = 0 := by
    rw [← Matrix.mulVecLin_mul, hC, Matrix.mulVecLin_zero]
  have hk := LinearMap.range_le_ker_iff.mpr hzero
  rw [heq] at hk
  have hcomp := LinearMap.range_le_ker_iff.mp hk
  apply Matrix.toLin'.injective
  simpa only [Matrix.toLin'_apply', Matrix.mulVecLin_mul, Matrix.mulVecLin_zero] using hcomp

theorem right_annihilator_of_equal_rank
    {m n k l : Type*} [Fintype m] [Fintype n] [Fintype k]
    (L : Matrix m k ℝ) (H : Matrix k n ℝ)
    (h : (L * H).rank = H.rank)
    (C : Matrix n l ℝ) (hC : (L * H) * C = 0) : H * C = 0 := by
  classical
  have ht : (Hᵀ * Lᵀ).rank = Hᵀ.rank := by
    rw [← Matrix.transpose_mul, Matrix.rank_transpose, Matrix.rank_transpose]
    exact h
  have hCt : Cᵀ * (Hᵀ * Lᵀ) = 0 := by
    rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, hC, Matrix.transpose_zero]
  have hz := left_annihilator_of_equal_rank Hᵀ Lᵀ ht Cᵀ hCt
  simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero]
    using congrArg Matrix.transpose hz

def balanceRow : Matrix (Fin 1) (Fin 4) ℝ := !![1, -1, 1, -1]

theorem intrinsic_column_balance {k : Type*} [Fintype k]
    (U : Matrix (Fin 4) k ℝ) (V : Matrix k (Fin 4) ℝ)
    (hr : (U * V).rank = U.rank)
    (hrel : ∀ j, (U * V) 0 j + (U * V) 2 j =
      (U * V) 1 j + (U * V) 3 j) :
    ∀ h, U 0 h + U 2 h = U 1 h + U 3 h := by
  have hz : balanceRow * (U * V) = 0 := by
    ext i j
    fin_cases i
    norm_num [balanceRow, Matrix.mul_apply, Fin.sum_univ_succ]
    have hj := hrel j
    simp only [Matrix.mul_apply] at hj
    linarith
  have hu := left_annihilator_of_equal_rank U V hr balanceRow hz
  intro h
  have hh := congrArg (fun M : Matrix (Fin 1) k ℝ => M 0 h) hu
  norm_num [balanceRow, Matrix.mul_apply, Fin.sum_univ_succ] at hh
  linarith

theorem intrinsic_row_balance {k : Type*} [Fintype k]
    (U : Matrix (Fin 4) k ℝ) (V : Matrix k (Fin 4) ℝ)
    (hr : (U * V).rank = V.rank)
    (hrel : ∀ i, (U * V) i 0 + (U * V) i 2 =
      (U * V) i 1 + (U * V) i 3) :
    ∀ h, V h 0 + V h 2 = V h 1 + V h 3 := by
  have hz : (U * V) * balanceRowᵀ = 0 := by
    ext i j
    fin_cases j
    norm_num [balanceRow, Matrix.mul_apply, Fin.sum_univ_succ]
    have hi := hrel i
    simp only [Matrix.mul_apply] at hi
    linarith
  have hv := right_annihilator_of_equal_rank U V hr balanceRowᵀ hz
  intro h
  have hh := congrArg (fun M : Matrix k (Fin 1) ℝ => M h 0) hv
  norm_num [balanceRow, Matrix.mul_apply, Fin.sum_univ_succ] at hh
  linarith

theorem score_bound_of_equal_factor_ranks {k : Type*} [Fintype k]
    (U : Matrix (Fin 4) k ℝ) (V : Matrix k (Fin 4) ℝ)
    (hU : EntryNonneg U) (hV : EntryNonneg V)
    (hu : (U * V).rank = U.rank) (hv : (U * V).rank = V.rank)
    (hrows : ∀ j, (U * V) 0 j + (U * V) 2 j =
      (U * V) 1 j + (U * V) 3 j)
    (hcols : ∀ i, (U * V) i 0 + (U * V) i 2 =
      (U * V) i 1 + (U * V) i 3) :
    ConeObstruction.score (U * V) ≤ ConeObstruction.mass (U * V) / 2 :=
  ConeObstruction.factorization_score_bound U V hU hV
    (intrinsic_column_balance U V hu hrows) (intrinsic_row_balance U V hv hcols)

theorem nested_nonneg (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    EntryNonneg (ConeObstruction.nested a) := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ConeObstruction.nested, ConeObstruction.twist] <;> linarith

theorem nested_balanced_parameter_le_half {k : Type*} [Fintype k]
    (a : ℝ) (U : Matrix (Fin 4) k ℝ) (V : Matrix k (Fin 4) ℝ)
    (hU : EntryNonneg U) (hV : EntryNonneg V) (hUV : U * V = ConeObstruction.nested a)
    (hu : U.rank = (ConeObstruction.nested a).rank)
    (hv : V.rank = (ConeObstruction.nested a).rank) : a ≤ (1 : ℝ) / 2 := by
  have hh := score_bound_of_equal_factor_ranks U V hU hV
    (by rw [hUV, hu]) (by rw [hUV, hv])
    (by intro j; rw [hUV]; fin_cases j <;>
      norm_num [ConeObstruction.nested, ConeObstruction.twist] <;> ring)
    (by intro i; rw [hUV]; fin_cases i <;>
      norm_num [ConeObstruction.nested, ConeObstruction.twist] <;> ring)
  rw [hUV, ConeObstruction.score_nested, ConeObstruction.mass_nested] at hh
  linarith

noncomputable def lowerLeft : Matrix (Fin 4) (Fin 4) ℝ :=
  !![2, 2, 0, 0; 0, 2, 2, 0; 0, 0, 2, 2; 2, 0, 0, 2]

noncomputable def lowerRight (a : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1/4+a/2, 1/4, 1/4-a/2, 1/4;
     1/4, 1/4+a/2, 1/4, 1/4-a/2;
     1/4-a/2, 1/4, 1/4+a/2, 1/4;
     1/4, 1/4-a/2, 1/4, 1/4+a/2]

theorem lower_factorization (a : ℝ) : lowerLeft * lowerRight a = ConeObstruction.nested a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [lowerLeft, lowerRight, ConeObstruction.nested, ConeObstruction.twist,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem rank_le_three_of_last_column (M : Matrix (Fin 4) (Fin 4) ℝ)
    (h : ∀ i, M i 3 = M i 0 - M i 1 + M i 2) : M.rank ≤ 3 := by
  let R : Matrix (Fin 4) (Fin 3) ℝ := M.submatrix id Fin.castSucc
  have hfac : R * seedRankRight = M := by
    ext i j
    fin_cases j <;>
      norm_num [R, Matrix.submatrix, seedRankRight, Matrix.mul_apply, Fin.sum_univ_succ] <;>
        linarith [h i]
  rw [← hfac]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)

theorem lower_factor_rank_bound (a : ℝ) (ha : 0 ≤ a) (ha2 : a ≤ (1 : ℝ) / 2) :
    HasFactorRankBound (ConeObstruction.nested a) 3 := by
  refine ⟨4, lowerLeft, lowerRight a, ?_, ?_, lower_factorization a, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [lowerLeft]
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [lowerRight] <;> linarith
  · apply rank_le_three_of_last_column
    intro i
    fin_cases i <;> norm_num [lowerLeft]
  · apply rank_le_three_of_last_column
    intro i
    fin_cases i <;> norm_num [lowerRight] <;> ring

/-- The minimum ordinary factor rank is exactly three up to and including
one half. In particular the endpoint has a nonnegative balanced factorization. -/
theorem nested_profile_low (a : ℝ) (ha : 0 < a) (ha2 : a ≤ (1 : ℝ) / 2) :
    factorRankProfile (ConeObstruction.nested a) = 3 := by
  have hA := nested_nonneg a ha.le (by linarith)
  have hlo := rank_le_factorRankProfile hA
  rw [nested_rank a (ne_of_gt ha)] at hlo
  exact le_antisymm (factorRankProfile_le_of_bound (lower_factor_rank_bound a ha.le ha2)) hlo

theorem nested_profile_high (a : ℝ) (ha : (1 : ℝ) / 2 < a) (ha1 : a ≤ 1) :
    factorRankProfile (ConeObstruction.nested a) = 4 := by
  have ha0 : 0 < a := by linarith
  have hA := nested_nonneg a ha0.le ha1
  have hr := nested_rank a (ne_of_gt ha0)
  have hup : factorRankProfile (ConeObstruction.nested a) ≤ 4 := by
    exact (factorRankProfile_le_nnrank hA).trans (by simpa using nnrank_le_card_width hA)
  have hlo := rank_le_factorRankProfile hA
  rw [hr] at hlo
  have hne : factorRankProfile (ConeObstruction.nested a) ≠ 3 := by
    intro heq
    obtain ⟨k, U, V, hU, hV, hUV, hUr, hVr⟩ := hasFactorRankBound_profile hA
    have hu := Matrix.rank_mul_le_left U V
    have hv := Matrix.rank_mul_le_right U V
    rw [hUV, hr] at hu hv
    rw [heq] at hUr hVr
    have hUr' : U.rank = (ConeObstruction.nested a).rank := by omega
    have hVr' : V.rank = (ConeObstruction.nested a).rank := by omega
    have hh := nested_balanced_parameter_le_half a U V hU hV hUV hUr' hVr'
    linarith
  omega

theorem nested_defect_low (a : ℝ) (ha : 0 < a) (ha2 : a ≤ (1 : ℝ) / 2) :
    factorRankDefect (ConeObstruction.nested a) = 0 := by
  rw [factorRankDefect, nested_profile_low a ha ha2, nested_rank a (ne_of_gt ha)]

theorem nested_defect_high (a : ℝ) (ha : (1 : ℝ) / 2 < a) (ha1 : a ≤ 1) :
    factorRankDefect (ConeObstruction.nested a) = 1 := by
  have ha0 : 0 < a := by linarith
  rw [factorRankDefect, nested_profile_high a ha ha1, nested_rank a (ne_of_gt ha0)]

theorem original_seed_profile : factorRankProfile MatCKronecker.seed = 4 := by
  have hup : factorRankProfile MatCKronecker.seed ≤ 4 := by
    exact (factorRankProfile_le_nnrank seed_nonneg).trans (by simpa using nnrank_le_card_width seed_nonneg)
  have hlo := rank_le_factorRankProfile seed_nonneg
  rw [seed_rank] at hlo
  have hne : factorRankProfile MatCKronecker.seed ≠ 3 := by
    intro heq
    obtain ⟨k, U, V, hU, hV, hUV, hUr, hVr⟩ := hasFactorRankBound_profile seed_nonneg
    have hu := Matrix.rank_mul_le_left U V
    have hv := Matrix.rank_mul_le_right U V
    rw [hUV, seed_rank] at hu hv
    rw [heq] at hUr hVr
    have hUr' : (U * V).rank = U.rank := by rw [hUV, seed_rank]; omega
    have hVr' : (U * V).rank = V.rank := by rw [hUV, seed_rank]; omega
    have hh := score_bound_of_equal_factor_ranks U V hU hV hUr' hVr'
      (by intro j; rw [hUV]; fin_cases j <;> norm_num [MatCKronecker.seed])
      (by intro i; rw [hUV]; fin_cases i <;> norm_num [MatCKronecker.seed])
    rw [hUV] at hh
    norm_num [ConeObstruction.score, ConeObstruction.mass, ConeObstruction.twist,
      MatCKronecker.seed, Fin.sum_univ_succ] at hh
  omega

theorem original_seed_defect : factorRankDefect MatCKronecker.seed = 1 := by
  rw [factorRankDefect, original_seed_profile, seed_rank]

end PositiveCore.ProfileExamples
