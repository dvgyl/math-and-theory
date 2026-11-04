module

public import PositiveCore.RankSaturation
public import PositiveCore.ConeObstruction
public import PositiveCore.OriginalMixedRank
public import PositiveCore.KroneckerRank
public import PositiveCore.RankProfile
public import MatCKronecker.Counterexample

@[expose] public section

namespace PositiveCore

open Matrix MatCKronecker
open scoped BigOperators Kronecker

/-- A linear relation among four rows of a rank-saturating product already
holds for the corresponding four rows of the left factor. -/
theorem four_row_relation_transfer
    {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
    (L : Matrix m k ℝ) (H : Matrix k n ℝ)
    (hsat : (L * H).rank = Fintype.card k)
    (a b c d : m)
    (hrel : ∀ j, (L * H) a j + (L * H) c j =
      (L * H) b j + (L * H) d j) :
    ∀ h, L a h + L c h = L b h + L d h := by
  classical
  obtain ⟨J, hJ⟩ := exists_right_inverse_of_full_row_rank H
    (saturated_factor_ranks L H hsat).2
  have hrec : (L * H) * J = L := by rw [Matrix.mul_assoc, hJ, Matrix.mul_one]
  intro h
  have hh : ((L * H) * J) a h + ((L * H) * J) c h =
      ((L * H) * J) b h + ((L * H) * J) d h := by
    change (∑ j, (L * H) a j * J j h) + (∑ j, (L * H) c j * J j h) =
      (∑ j, (L * H) b j * J j h) + (∑ j, (L * H) d j * J j h)
    simp only [← Finset.sum_add_distrib, ← add_mul]
    exact Finset.sum_congr rfl (fun j _ => congrArg (fun x => x * J j h) (hrel j))
  simpa only [hrec] using hh

/-- The analogous transfer of a four-column relation to the right factor. -/
theorem four_column_relation_transfer
    {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
    (L : Matrix m k ℝ) (H : Matrix k n ℝ)
    (hsat : (L * H).rank = Fintype.card k)
    (a b c d : n)
    (hrel : ∀ i, (L * H) i a + (L * H) i c =
      (L * H) i b + (L * H) i d) :
    ∀ h, H h a + H h c = H h b + H h d := by
  classical
  obtain ⟨J, hJ⟩ := exists_left_inverse_of_full_column_rank L
    (saturated_factor_ranks L H hsat).1
  have hrec : J * (L * H) = H := by rw [← Matrix.mul_assoc, hJ, Matrix.one_mul]
  intro h
  have hh : (J * (L * H)) h a + (J * (L * H)) h c =
      (J * (L * H)) h b + (J * (L * H)) h d := by
    change (∑ i, J h i * (L * H) i a) + (∑ i, J h i * (L * H) i c) =
      (∑ i, J h i * (L * H) i b) + (∑ i, J h i * (L * H) i d)
    simp only [← Finset.sum_add_distrib, ← mul_add]
    exact Finset.sum_congr rfl (fun i _ => congrArg (fun x => J h i * x) (hrel i))
  simpa only [hrec] using hh

/-- A separating functional on the intrinsic nonnegative row/column cones
prevents EVERY nonzero nonnegative auxiliary matrix from attaining ordinary
rank in the Kronecker product.  This theorem does not assume a special form or
size for the auxiliary factor. -/
theorem tensor_obstruction_of_score
    {s t : Type*} [Fintype s] [Fintype t]
    (A : Matrix (Fin 4) (Fin 4) ℝ) (B : Matrix s t ℝ)
    (hA : EntryNonneg A) (hB : EntryNonneg B)
    (hrows : ∀ j, A 0 j + A 2 j = A 1 j + A 3 j)
    (hcols : ∀ i, A i 0 + A i 2 = A i 1 + A i 3)
    (hscore : ConeObstruction.mass A / 2 < ConeObstruction.score A)
    (i0 : s) (j0 : t) (hpos : 0 < B i0 j0) :
    (A ⊗ₖ B).rank < nnrank (A ⊗ₖ B) := by
  classical
  have hM := hA.kronecker hB
  have hlo := rank_le_nnrank hM
  by_contra hnot
  have heq : nnrank (A ⊗ₖ B) = (A ⊗ₖ B).rank := by omega
  obtain ⟨L, H, hL, hH, hLH⟩ := hasNMF_nnrank hM
  have hsat : (L * H).rank = Fintype.card (Fin (nnrank (A ⊗ₖ B))) := by
    rw [hLH]
    simpa using heq.symm
  let U : Matrix (Fin 4) (Fin (nnrank (A ⊗ₖ B))) ℝ := fun i h => L (i, i0) h
  let V : Matrix (Fin (nnrank (A ⊗ₖ B))) (Fin 4) ℝ := fun h j => H h (j, j0)
  have hU : EntryNonneg U := fun i h => hL (i, i0) h
  have hV : EntryNonneg V := fun h j => hH h (j, j0)
  have hu : ∀ h, U 0 h + U 2 h = U 1 h + U 3 h := by
    apply four_row_relation_transfer L H hsat (0, i0) (1, i0) (2, i0) (3, i0)
    intro j
    rw [hLH]
    change A 0 j.1 * B i0 j.2 + A 2 j.1 * B i0 j.2 =
      A 1 j.1 * B i0 j.2 + A 3 j.1 * B i0 j.2
    rw [← add_mul, ← add_mul, hrows j.1]
  have hv : ∀ h, V h 0 + V h 2 = V h 1 + V h 3 := by
    apply four_column_relation_transfer L H hsat (0, j0) (1, j0) (2, j0) (3, j0)
    intro i
    rw [hLH]
    change A i.1 0 * B i.2 j0 + A i.1 2 * B i.2 j0 =
      A i.1 1 * B i.2 j0 + A i.1 3 * B i.2 j0
    rw [← add_mul, ← add_mul, hcols i.1]
  have hUV : U * V = (B i0 j0) • A := by
    ext i j
    change (L * H) (i, i0) (j, j0) = B i0 j0 * A i j
    rw [hLH]
    simp only [Matrix.kronecker_apply]
    ring
  have hb := ConeObstruction.factorization_score_bound U V hU hV hu hv
  rw [hUV] at hb
  have hscore_scale : ConeObstruction.score ((B i0 j0) • A) =
      B i0 j0 * ConeObstruction.score A := by
    simp only [ConeObstruction.score, Matrix.smul_apply, smul_eq_mul]
    simp_rw [mul_left_comm (ConeObstruction.twist _ _), ← Finset.mul_sum]
  have hmass_scale : ConeObstruction.mass ((B i0 j0) • A) =
      B i0 j0 * ConeObstruction.mass A := by
    simp only [ConeObstruction.mass, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  rw [hscore_scale, hmass_scale] at hb
  nlinarith

/-- Ordinary rank of every nontrivial nested-square matrix. -/
theorem nested_rank (a : ℝ) (ha : a ≠ 0) :
    (ConeObstruction.nested a).rank = 3 := by
  let R : Matrix (Fin 4) (Fin 3) ℝ :=
    fun i j => ConeObstruction.nested a i j.castSucc
  have hfac : R * seedRankRight = ConeObstruction.nested a := by
    ext i j
    change (∑ h, R i h * seedRankRight h j) = ConeObstruction.nested a i j
    fin_cases i <;> fin_cases j <;>
      norm_num [R, seedRankRight, ConeObstruction.nested, ConeObstruction.twist,
        Fin.sum_univ_succ] <;> ring
  let M : Matrix (Fin 3) (Fin 3) ℝ :=
    (ConeObstruction.nested a).submatrix Fin.castSucc Fin.castSucc
  have hdet : M.det = 8 * a ^ 2 := by
    norm_num [M, Matrix.det_fin_three, Matrix.submatrix, ConeObstruction.nested,
      ConeObstruction.twist] <;> ring
  apply le_antisymm
  · rw [← hfac]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)
  · have hm : M.rank = 3 := by
      have hn : M.det ≠ 0 := by
        rw [hdet]
        exact mul_ne_zero (by norm_num) (pow_ne_zero _ ha)
      simpa using Matrix.rank_of_det_ne_zero hn
    rw [← hm]
    exact Matrix.rank_submatrix_le _ Fin.castSucc Fin.castSucc

/-- Above one half, no nonzero nonnegative tensor partner can attain the
ordinary rank. The auxiliary factor may be rectangular and of arbitrary size. -/
theorem nested_tensor_obstruction
    {s t : Type*} [Fintype s] [Fintype t]
    (a : ℝ) (ha : (1 : ℝ) / 2 < a) (ha1 : a ≤ 1)
    (B : Matrix s t ℝ) (hB : EntryNonneg B) (hBne : B ≠ 0) :
    3 * B.rank < nnrank (ConeObstruction.nested a ⊗ₖ B) := by
  have ha0 : 0 < a := by linarith
  have hA : EntryNonneg (ConeObstruction.nested a) := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [ConeObstruction.nested, ConeObstruction.twist] <;> linarith
  obtain ⟨i0, j0, hpos⟩ := exists_positive_entry_of_nonzero hB hBne
  have hh : (ConeObstruction.nested a ⊗ₖ B).rank <
      nnrank (ConeObstruction.nested a ⊗ₖ B) := by
    apply tensor_obstruction_of_score (ConeObstruction.nested a) B hA hB
      (i0 := i0) (j0 := j0)
    · intro j
      fin_cases j <;> norm_num [ConeObstruction.nested, ConeObstruction.twist] <;> ring
    · intro i
      fin_cases i <;> norm_num [ConeObstruction.nested, ConeObstruction.twist] <;> ring
    · rw [ConeObstruction.score_nested, ConeObstruction.mass_nested]
      linarith
    · exact hpos
  simpa only [rank_kronecker, nested_rank a (ne_of_gt ha0)] using hh

/-- The original 17/1 seed cannot have a rank-saturating tensor product with
any nonzero nonnegative auxiliary matrix. -/
theorem original_seed_tensor_obstruction
    {s t : Type*} [Fintype s] [Fintype t]
    (B : Matrix s t ℝ) (hB : EntryNonneg B)
    (i0 : s) (j0 : t) (hpos : 0 < B i0 j0) :
    (MatCKronecker.seed ⊗ₖ B).rank < nnrank (MatCKronecker.seed ⊗ₖ B) := by
  apply tensor_obstruction_of_score MatCKronecker.seed B seed_nonneg hB
    (i0 := i0) (j0 := j0)
  · intro j
    fin_cases j <;> norm_num [MatCKronecker.seed]
  · intro i
    fin_cases i <;> norm_num [MatCKronecker.seed]
  · norm_num [ConeObstruction.mass, ConeObstruction.score, ConeObstruction.twist,
      MatCKronecker.seed, Fin.sum_univ_succ]
  · exact hpos

/-- The original mixed-block upper bound is sharp for every family parameter.
This resolves the two-value ambiguity explicitly left open in the original
manuscript. -/
theorem original_mixed_nnrank_exact {t : ℕ} (ht : 0 < t) :
    nnrank (MatCKronecker.seed ⊗ₖ smallBlock t) = 3 * t + 4 := by
  have hup := nnrank_le_of_hasNMF (cross_hasNMF ht)
  have hpos : 0 < smallBlock t none none := by
    change 0 < 1 + crossEpsilon t
    linarith [crossEpsilon_pos ht]
  have hlo := original_seed_tensor_obstruction (smallBlock t) (smallBlock_nonneg ht)
    none none hpos
  rw [original_mixed_rank ht] at hlo
  omega

/-- The exact mixed-block value also holds with the two tensor factors swapped. -/
theorem original_mixed_nnrank_exact_reverse {t : ℕ} (ht : 0 < t) :
    nnrank (smallBlock t ⊗ₖ MatCKronecker.seed) = 3 * t + 4 := by
  rw [(kronecker_swap_ranks MatCKronecker.seed (smallBlock t)
    seed_nonneg (smallBlock_nonneg ht)).2]
  exact original_mixed_nnrank_exact ht

end PositiveCore
