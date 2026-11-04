module

public import MatCKronecker.CrossData
public import MatCKronecker.SimplexUniform
public import MatCKronecker.PositiveIdentity

@[expose] public section

namespace MatCKronecker

open Matrix
open scoped Kronecker

noncomputable def smallBlock (t : ℕ) : Matrix (Option (Fin t)) (Option (Fin t)) ℝ :=
  nearOne (Option (Fin t)) (crossEpsilon t)

noncomputable def baselineScale (t : ℕ) : ℝ := 1 + crossEpsilon t / ((t : ℝ) + 1)

noncomputable def crossU (t : ℕ) : (Fin 4 × Option (Fin t)) → ℝ :=
  fun i => seedLeft i.1 0

noncomputable def crossV (t : ℕ) : (Fin 4 × Option (Fin t)) → ℝ :=
  fun j => baselineScale t * seedRight 0 j.1

noncomputable def otherLeft (t : ℕ) : Matrix (Fin 4 × Option (Fin t)) (Fin 3) ℝ :=
  fun i k => seedLeft i.1 k.succ

noncomputable def otherRight (t : ℕ) : Matrix (Fin 3) (Fin 4 × Option (Fin t)) ℝ :=
  fun k j => baselineScale t * seedRight k.succ j.1

noncomputable def correctedTerm (t : ℕ) :
    Matrix (Fin 4 × Option (Fin t)) (Fin 4 × Option (Fin t)) ℝ :=
  Matrix.vecMulVec (crossU t) (crossV t) + crossEpsilon t • (seed ⊗ₖ centeredIdentity t)

theorem baselineScale_ge_one {t : ℕ} (ht : 0 < t) : 1 ≤ baselineScale t := by
  unfold baselineScale
  have h : 0 ≤ crossEpsilon t / ((t : ℝ) + 1) := by
    exact div_nonneg (crossEpsilon_pos ht).le (by positivity)
  linarith

theorem crossU_lower (t : ℕ) (i : Fin 4 × Option (Fin t)) :
    (1 : ℝ) / 36 ≤ crossU t i := seedLeft_lower i.1 0

theorem crossV_lower {t : ℕ} (ht : 0 < t) (j : Fin 4 × Option (Fin t)) :
    (1 : ℝ) / 10 ≤ crossV t j := by
  have hs := baselineScale_ge_one ht
  have hv := seedRight_lower 0 j.1
  dsimp [crossV]
  nlinarith

theorem correctedTerm_hasNMF {t : ℕ} (ht : 0 < t) :
    HasNMF (correctedTerm t) (3 * t + 1) := by
  have hc : Fintype.card (Fin 3 × Fin t) = 3 * t := by simp
  have hp : 0 < Fintype.card (Fin 3 × Fin t) := by rw [hc]; omega
  have hL : EntryNonneg (simplexLeft (crossU t) (crossRankLeft t) (crossEta t)) := by
    simpa [crossEta] using simplexLeft_nonneg_uniform hp (crossU t) (crossRankLeft t)
      (crossU_lower t) (crossRankLeft_abs_le t)
  have hR : EntryNonneg (simplexRight (crossV t) (crossRankRight t)
      (crossEpsilon t) (crossEta t)) := by
    simpa [crossEpsilon, crossEta] using simplexRight_nonneg_uniform hp
      (crossV t) (crossRankRight t) (crossV_lower ht) (crossRankRight_abs_le t)
  have hmul : simplexLeft (crossU t) (crossRankLeft t) (crossEta t) *
      simplexRight (crossV t) (crossRankRight t) (crossEpsilon t) (crossEta t) =
      correctedTerm t := by
    rw [simplex_factorization _ _ _ _ _ _ (ne_of_gt (crossEta_pos ht)),
      cross_rank_factorization]
    rfl
  have h := hasNMF_of_factorization _ _ hL hR hmul
  simpa [hc] using h

theorem other_hasNMF {t : ℕ} (ht : 0 < t) :
    HasNMF (otherLeft t * otherRight t) 3 := by
  have hL : EntryNonneg (otherLeft t) := by
    intro i k
    exact le_trans (by norm_num : (0 : ℝ) ≤ 1 / 36) (seedLeft_lower i.1 k.succ)
  have hR : EntryNonneg (otherRight t) := by
    intro k j
    exact mul_nonneg (le_trans (by norm_num) (baselineScale_ge_one ht))
      (le_trans (by norm_num : (0 : ℝ) ≤ 1 / 10) (seedRight_lower k.succ j.1))
  simpa using hasNMF_of_factorization (otherLeft t) (otherRight t) hL hR rfl

theorem other_plus_main (t : ℕ) (i j : Fin 4 × Option (Fin t)) :
    (otherLeft t * otherRight t) i j + crossU t i * crossV t j =
      baselineScale t * seed i.1 j.1 := by
  have hs := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M i.1 j.1)
    seed_nonnegative_factorization
  simp only [Matrix.mul_apply, Fin.sum_univ_succ] at hs
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, otherLeft, otherRight, crossU, crossV]
  linear_combination (baselineScale t) * hs

theorem cross_factorization_identity (t : ℕ) :
    otherLeft t * otherRight t + correctedTerm t = seed ⊗ₖ smallBlock t := by
  ext i j
  calc
    (otherLeft t * otherRight t + correctedTerm t) i j =
        ((otherLeft t * otherRight t) i j + crossU t i * crossV t j) +
          crossEpsilon t * (seed i.1 j.1 * centeredIdentity t i.2 j.2) := by
      simp [correctedTerm, Matrix.vecMulVec_apply, add_assoc]
    _ = baselineScale t * seed i.1 j.1 +
          crossEpsilon t * (seed i.1 j.1 * centeredIdentity t i.2 j.2) := by
      rw [other_plus_main]
    _ = (seed ⊗ₖ smallBlock t) i j := by
      simp only [Matrix.kroneckerMap_apply, baselineScale, centeredIdentity, smallBlock, nearOne]
      split_ifs <;> ring

theorem cross_hasNMF {t : ℕ} (ht : 0 < t) :
    HasNMF (seed ⊗ₖ smallBlock t) (3 * t + 4) := by
  have h := (other_hasNMF ht).add (correctedTerm_hasNMF ht)
  rw [cross_factorization_identity] at h
  convert h using 1; omega

end MatCKronecker
