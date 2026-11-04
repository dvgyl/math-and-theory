module

public import PositiveCore.NullspaceAbsorption
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.Notation

@[expose] public section

namespace PositiveCore.Activation

open Matrix MatCKronecker
open scoped BigOperators Kronecker

set_option maxHeartbeats 4000000

/-!
# An exact positive mixed product of ordinary and nonnegative rank six

The upper bound is checked by the Lean kernel for every real ε in the
stated interval, rather than imported from the external rational certificates.
The four-by-four seed's nonnegative rank four is NOT asserted in this module;
its classical nested-squares lower bound is cited in the manuscript.
-/

/-- The rational nested-square seed with parameter 9/20. -/
noncomputable def seed : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(29 / 20), (29 / 20), (11 / 20), (11 / 20);
     (11 / 20), (29 / 20), (29 / 20), (11 / 20);
     (11 / 20), (11 / 20), (29 / 20), (29 / 20);
     (29 / 20), (11 / 20), (11 / 20), (29 / 20)]

noncomputable def auxiliary (ε : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 + ε, 1; 1, 1 + ε]

/-- The four rows with auxiliary row index zero. -/
noncomputable def leftEven : Matrix (Fin 4) (Fin 6) ℝ :=
  !![(81707 / 41760), (81491 / 41760), (81359 / 41760), (187 / 96), (5 / 96), (23 / 480);
     (2237 / 41760), (2237 / 41760), (1889 / 41760), (27133 / 13920), (5431 / 2784), (137 / 2784);
     (2093 / 41760), (2309 / 41760), (1961 / 41760), (137 / 2784), (5431 / 2784), (27133 / 13920);
     (81563 / 41760), (81563 / 41760), (81431 / 41760), (23 / 480), (5 / 96), (187 / 96)]

/-- The four rows with auxiliary row index one. -/
noncomputable def leftOdd : Matrix (Fin 4) (Fin 6) ℝ :=
  !![(81157 / 41760), (81373 / 41760), (16301 / 8352), (937 / 480), (23 / 480), (5 / 96);
     (1939 / 41760), (1939 / 41760), (2287 / 41760), (5431 / 2784), (27133 / 13920), (707 / 13920);
     (2083 / 41760), (1867 / 41760), (443 / 8352), (707 / 13920), (27133 / 13920), (5431 / 2784);
     (81301 / 41760), (81301 / 41760), (81433 / 41760), (5 / 96), (23 / 480), (937 / 480)]

/-- The constant coefficient of the right factor. -/
noncomputable def rightConstant : Matrix (Fin 6) (Fin 4) ℝ :=
  !![(37 / 228), (1 / 12), (1 / 228), (1 / 12);
     (37 / 228), (1 / 12), (1 / 228), (1 / 12);
     (37 / 228), (1 / 12), (1 / 228), (1 / 12);
     (1 / 4), (37 / 76), (1 / 4), (1 / 76);
     (1 / 76), (1 / 4), (37 / 76), (1 / 4);
     (1 / 4), (1 / 76), (1 / 4), (37 / 76)]

/-- The ε coefficient in auxiliary column zero. -/
noncomputable def rightEvenSlope : Matrix (Fin 6) (Fin 4) ℝ :=
  !![(13261 / 456), (2089 / 24), (1 / 456), (-1391 / 24);
     (13261 / 456), (1 / 24), (39673 / 456), (2785 / 24);
     (13261 / 456), (-2087 / 24), (-39671 / 456), (697 / 24);
     (-695 / 8), (37 / 152), (1 / 8), (-13223 / 152);
     (13225 / 152), (1 / 8), (37 / 152), (697 / 8);
     (-695 / 8), (1 / 152), (1 / 8), (-13187 / 152)]

/-- The ε coefficient in auxiliary column one. -/
noncomputable def rightOddSlope : Matrix (Fin 6) (Fin 4) ℝ :=
  !![(-13187 / 456), (-2087 / 24), (1 / 456), (1393 / 24);
     (-13187 / 456), (1 / 24), (-39671 / 456), (-2783 / 24);
     (-13187 / 456), (2089 / 24), (39673 / 456), (-695 / 24);
     (697 / 8), (37 / 152), (1 / 8), (13225 / 152);
     (-13223 / 152), (1 / 8), (37 / 152), (-695 / 8);
     (697 / 8), (1 / 152), (1 / 8), (13261 / 152)]

noncomputable def left : Matrix (Fin 4 × Fin 2) (Fin 6) ℝ :=
  fun i h => if i.2 = 0 then leftEven i.1 h else leftOdd i.1 h

noncomputable def right (ε : ℝ) : Matrix (Fin 6) (Fin 4 × Fin 2) ℝ :=
  fun h j => rightConstant h j.1 + ε *
    (if j.2 = 0 then rightEvenSlope h j.1 else rightOddSlope h j.1)

/-- The parameterized factorization identity is exact over the real numbers. -/
theorem product_identity (ε : ℝ) : left * right ε = seed ⊗ₖ auxiliary ε := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases i <;> fin_cases a <;> fin_cases j <;> fin_cases b <;>
    norm_num [left, right, leftEven, leftOdd, rightConstant,
      rightEvenSlope, rightOddSlope, seed, auxiliary,
      Matrix.mul_apply, Fin.sum_univ_succ, Matrix.kronecker_apply] <;> ring

/-- Uniform strict positivity of the left factor. -/
theorem left_positive (i : Fin 4 × Fin 2) (h : Fin 6) : 0 < left i h := by
  rcases i with ⟨i, a⟩
  fin_cases i <;> fin_cases a <;> fin_cases h <;>
    norm_num [left, leftEven, leftOdd]

/-- Uniform strict positivity of the right factor on the explicit interval. -/
theorem right_positive (ε : ℝ) (hε : 0 ≤ ε) (hεb : ε ≤ (1 : ℝ) / 238032)
    (h : Fin 6) (j : Fin 4 × Fin 2) : 0 < right ε h j := by
  rcases j with ⟨j, b⟩
  fin_cases h <;> fin_cases j <;> fin_cases b <;>
    norm_num [right, rightConstant, rightEvenSlope, rightOddSlope] <;> linarith

/-- A real nonnegative factorization of width six, not merely a numerical rank claim. -/
theorem hasNMF_six (ε : ℝ) (hε : 0 ≤ ε) (hεb : ε ≤ (1 : ℝ) / 238032) :
    HasNMF (seed ⊗ₖ auxiliary ε) 6 := by
  refine ⟨left, right ε, ?_, ?_, product_identity ε⟩
  · exact fun i h => (left_positive i h).le
  · exact fun h j => (right_positive ε hε hεb h j).le

noncomputable def seedMinor : Matrix (Fin 3) (Fin 3) ℝ :=
  seed.submatrix Fin.castSucc Fin.castSucc

/-- An exact nonsingular minor of the seed. -/
theorem seedMinor_det : seedMinor.det = (81 : ℝ) / 50 := by
  norm_num [seedMinor, seed, Matrix.submatrix, Matrix.det_fin_three]

/-- The auxiliary matrix is invertible for every positive parameter. -/
theorem auxiliary_det (ε : ℝ) : (auxiliary ε).det = ε * (ε + 2) := by
  simp [auxiliary, Matrix.det_fin_two]
  ring

noncomputable def seedRankLeft : Matrix (Fin 4) (Fin 3) ℝ :=
  seed.submatrix id Fin.castSucc

noncomputable def seedRankRight : Matrix (Fin 3) (Fin 4) ℝ :=
  !![1, 0, 0, 1; 0, 1, 0, -1; 0, 0, 1, 1]

theorem seed_rank_factorization : seedRankLeft * seedRankRight = seed := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [seedRankLeft, seedRankRight, seed, Matrix.submatrix,
      Matrix.mul_apply, Fin.sum_univ_succ]

theorem seed_rank : seed.rank = 3 := by
  apply le_antisymm
  · rw [← seed_rank_factorization]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)
  · have hm : seedMinor.rank = 3 := by
      have hd : seedMinor.det ≠ 0 := by rw [seedMinor_det]; norm_num
      simpa using Matrix.rank_of_det_ne_zero hd
    rw [← hm]
    exact Matrix.rank_submatrix_le seed Fin.castSucc Fin.castSucc

theorem auxiliary_rank (ε : ℝ) (hε : 0 < ε) : (auxiliary ε).rank = 2 := by
  have hd : (auxiliary ε).det ≠ 0 := by
    rw [auxiliary_det]
    exact ne_of_gt (mul_pos hε (by linarith))
  simpa using Matrix.rank_of_det_ne_zero hd

/-- The six-by-six tensor minor supplies the ordinary-rank lower bound. -/
theorem product_rank_lower (ε : ℝ) (hε : 0 < ε) :
    6 ≤ (seed ⊗ₖ auxiliary ε).rank := by
  have hd : (seedMinor ⊗ₖ auxiliary ε).det ≠ 0 := by
    rw [Matrix.det_kronecker, seedMinor_det, auxiliary_det]
    apply mul_ne_zero
    · norm_num
    · exact pow_ne_zero _ (ne_of_gt (mul_pos hε (by linarith)))
  have hm : (seedMinor ⊗ₖ auxiliary ε).rank = 6 := by
    simpa using Matrix.rank_of_det_ne_zero hd
  let f : Fin 3 × Fin 2 → Fin 4 × Fin 2 := fun i => (i.1.castSucc, i.2)
  have he : seedMinor ⊗ₖ auxiliary ε = (seed ⊗ₖ auxiliary ε).submatrix f f := by
    rfl
  rw [← hm, he]
  exact Matrix.rank_submatrix_le _ f f

/-- Exact real nonnegative rank six throughout a rationally specified interval. -/
theorem product_nnrank (ε : ℝ) (hε : 0 < ε) (hεb : ε ≤ (1 : ℝ) / 238032) :
    nnrank (seed ⊗ₖ auxiliary ε) = 6 := by
  apply le_antisymm
  · exact nnrank_le_of_hasNMF (hasNMF_six ε hε.le hεb)
  · exact (product_rank_lower ε hε).trans
      (rank_le_nnrank (hasNMF_six ε hε.le hεb).nonneg)

/-- Ordinary and nonnegative rank coincide for this genuinely perturbed product. -/
theorem product_rank (ε : ℝ) (hε : 0 < ε) (hεb : ε ≤ (1 : ℝ) / 238032) :
    (seed ⊗ₖ auxiliary ε).rank = 6 := by
  exact le_antisymm (hasNMF_six ε hε.le hεb).rank_le (product_rank_lower ε hε)

end PositiveCore.Activation
