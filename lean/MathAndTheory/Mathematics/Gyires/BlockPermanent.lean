module

public import MathAndTheory.Mathematics.Gyires.PermanentPermutation
public import MathAndTheory.Mathematics.Gyires.PermanentCauchySchwarz
public import MathAndTheory.Mathematics.Gyires.DimensionConstant
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Matrix.Block
public import Mathlib.Logic.Equiv.Basic

@[expose] public section

namespace MathAndTheory.Gyires

open scoped BigOperators
open Finset

variable {ι : Type*} {κ : ι → Type*}

lemma perm_eq_sigmaCongrRight_of_fst (σ : Equiv.Perm (Sigma κ))
    (hσ : ∀ x, (σ x).1 = x.1) :
    ∃ τ : ∀ i, Equiv.Perm (κ i), Equiv.sigmaCongrRight τ = σ := by
  let τ : ∀ i, Equiv.Perm (κ i) := fun i =>
    ((Equiv.sigmaSubtype i).symm.trans
      (σ.subtypePerm (p := fun x => x.1 = i) (by intro x; rw [hσ]))).trans
        (Equiv.sigmaSubtype i)
  refine ⟨τ, ?_⟩
  apply Equiv.ext
  rintro ⟨i, j⟩
  change Sigma.mk i (Equiv.sigmaSubtype i
    (σ.subtypePerm (p := fun x => x.1 = i) (by intro x; rw [hσ]) ⟨⟨i, j⟩, rfl⟩)) = σ ⟨i, j⟩
  have h := (Equiv.sigmaSubtype i).symm_apply_apply
    (σ.subtypePerm (p := fun x => x.1 = i) (by intro x; rw [hσ]) ⟨⟨i, j⟩, rfl⟩)
  exact congrArg Subtype.val h

variable [Fintype ι] [DecidableEq ι] [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

set_option maxHeartbeats 800000 in
/-- The permanent of a block diagonal matrix is the product of its block permanents. -/
theorem permanent_blockDiagonal (A : ∀ i, Matrix (κ i) (κ i) ℝ) :
    (Matrix.blockDiagonal' A).permanent = ∏ i, (A i).permanent := by
  classical
  let e : (∀ i, Equiv.Perm (κ i)) ↪ Equiv.Perm (Sigma κ) :=
    ⟨Equiv.sigmaCongrRight, Equiv.Perm.sigmaCongrRightHom_injective⟩
  let S := Finset.univ.map e
  have hzero : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm (Sigma κ))), σ ∉ S →
      (∏ x, Matrix.blockDiagonal' A (σ x) x) = 0 := by
    intro σ _ hnot
    by_contra hprod
    have hfst : ∀ x, (σ x).1 = x.1 := by
      intro x
      by_contra hne
      have hz : Matrix.blockDiagonal' A (σ x) x = 0 := by
        simp only [Matrix.blockDiagonal'_apply, dite_eq_right hne]
      exact hprod (Finset.prod_eq_zero (Finset.mem_univ x) hz)
    obtain ⟨τ, hτ⟩ := perm_eq_sigmaCongrRight_of_fst σ hfst
    exact hnot (Finset.mem_map.mpr ⟨τ, Finset.mem_univ _, hτ⟩)
  unfold Matrix.permanent
  calc
    _ = ∑ σ ∈ S, ∏ x, Matrix.blockDiagonal' A (σ x) x :=
      (Finset.sum_subset (Finset.subset_univ S) hzero).symm
    _ = ∑ τ : ∀ i, Equiv.Perm (κ i), ∏ i, ∏ j, A i (τ i j) j := by
      simp only [S, Finset.sum_map]
      apply Finset.sum_congr rfl
      intro τ _
      change (∏ x, Matrix.blockDiagonal' A (Equiv.sigmaCongrRight τ x) x) = _
      rw [Fintype.prod_sigma]
      simp only [Equiv.sigmaCongrRight_apply, Matrix.blockDiagonal'_apply_eq]
    _ = ∏ i, ∑ τ : Equiv.Perm (κ i), ∏ j, A i (τ j) j :=
      (Fintype.prod_sum (fun i (τ : Equiv.Perm (κ i)) => ∏ j, A i (τ j) j)).symm

omit [DecidableEq ι] [∀ i, DecidableEq (κ i)] in
lemma dimensionConstant_card_sigma_le (hsize : ∀ i, 0 < Fintype.card (κ i)) :
    dimensionConstant (Fintype.card (Sigma κ)) ≤
      ∏ i, dimensionConstant (Fintype.card (κ i)) := by
  let dims := (Finset.univ : Finset ι).toList.map (fun i => Fintype.card (κ i))
  have hpos : ∀ n ∈ dims, 0 < n := by
    intro n hn
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hn
    exact hsize i
  have h := dimensionConstant_sum_le dims hpos
  simpa only [dims, Finset.sum_map_toList, Fintype.card_sigma, List.map_map,
    Function.comp_def, Finset.prod_map_toList] using h

omit [DecidableEq ι] [∀ i, DecidableEq (κ i)] in
lemma dimensionConstant_card_sigma_lt (hsize : ∀ i, 0 < Fintype.card (κ i))
    (hblocks : 2 ≤ Fintype.card ι) :
    dimensionConstant (Fintype.card (Sigma κ)) <
      ∏ i, dimensionConstant (Fintype.card (κ i)) := by
  let dims := (Finset.univ : Finset ι).toList.map (fun i => Fintype.card (κ i))
  have hpos : ∀ n ∈ dims, 0 < n := by
    intro n hn
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hn
    exact hsize i
  have hlen : 2 ≤ dims.length := by simpa [dims] using hblocks
  have h : dimensionConstant dims.sum < (dims.map dimensionConstant).prod := by
    generalize hd : dims = ds at hpos hlen ⊢
    cases ds with
    | nil => simp at hlen
    | cons a rest =>
      cases rest with
      | nil => simp at hlen
      | cons b rest => exact dimensionConstant_sum_lt a b rest hpos
  simpa only [dims, Finset.sum_map_toList, Fintype.card_sigma, List.map_map,
    Function.comp_def, Finset.prod_map_toList] using h

omit [∀ i, DecidableEq (κ i)] in
lemma blockDiagonal_gram (A : ∀ i, Matrix (κ i) (κ i) ℝ) :
    Matrix.blockDiagonal' A * (Matrix.blockDiagonal' A).transpose =
      Matrix.blockDiagonal' (fun i => A i * (A i).transpose) := by
  rw [Matrix.blockDiagonal'_transpose, ← Matrix.blockDiagonal'_mul]

omit [∀ i, DecidableEq (κ i)] in
lemma blockDiagonal_transpose_gram (A : ∀ i, Matrix (κ i) (κ i) ℝ) :
    (Matrix.blockDiagonal' A).transpose * Matrix.blockDiagonal' A =
      Matrix.blockDiagonal' (fun i => (A i).transpose * A i) := by
  rw [Matrix.blockDiagonal'_transpose, ← Matrix.blockDiagonal'_mul]

/-- A block diagonal sum of doubly stochastic matrices is doubly stochastic. -/
theorem blockDiagonal_mem_doublyStochastic (A : ∀ i, Matrix (κ i) (κ i) ℝ)
    (hA : ∀ i, A i ∈ doublyStochastic ℝ (κ i)) :
    Matrix.blockDiagonal' A ∈ doublyStochastic ℝ (Sigma κ) := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨i, x⟩ ⟨j, y⟩
    by_cases hij : i = j
    · subst j
      simpa only [Matrix.blockDiagonal'_apply_eq] using (hA i).1 x y
    · simp only [Matrix.blockDiagonal'_apply_ne _ _ _ hij, le_refl]
  · rintro ⟨i, x⟩
    rw [Fintype.sum_sigma]
    calc
      (∑ j, ∑ y, Matrix.blockDiagonal' A ⟨i, x⟩ ⟨j, y⟩) = ∑ y, A i x y := by
        rw [Finset.sum_eq_single i]
        · simp only [Matrix.blockDiagonal'_apply_eq]
        · intro j _ hji
          simp only [Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hji), sum_const_zero]
        · simp
      _ = 1 := sum_row_of_mem_doublyStochastic (hA i) x
  · rintro ⟨i, x⟩
    rw [Fintype.sum_sigma]
    calc
      (∑ j, ∑ y, Matrix.blockDiagonal' A ⟨j, y⟩ ⟨i, x⟩) = ∑ y, A i y x := by
        rw [Finset.sum_eq_single i]
        · simp only [Matrix.blockDiagonal'_apply_eq]
        · intro j _ hji
          simp only [Matrix.blockDiagonal'_apply_ne _ _ _ hji, sum_const_zero]
        · simp
      _ = 1 := sum_col_of_mem_doublyStochastic (hA i) x

/-- A doubly stochastic matrix has a positive Gram permanent. -/
theorem permanent_gram_pos_of_doublyStochastic {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A ∈ doublyStochastic ℝ n) :
    0 < (A * A.transpose).permanent := by
  have hentry : ∀ i j, 0 ≤ (A * A.transpose) i j := by
    intro i j
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (hA.1 i k) (hA.1 j k))
  have hdiag : ∀ i, 0 < (A * A.transpose) i i := by
    intro i
    have hsum : 0 < ∑ j, A i j := by
      rw [sum_row_of_mem_doublyStochastic hA i]
      norm_num
    obtain ⟨j, _, hj⟩ := (Finset.sum_pos_iff_of_nonneg (fun j _ => hA.1 i j)).1 hsum
    apply Finset.sum_pos'
    · intro k _
      exact mul_self_nonneg (A i k)
    · exact ⟨j, Finset.mem_univ _, mul_pos hj hj⟩
  unfold Matrix.permanent
  apply Finset.sum_pos'
  · intro σ _
    exact Finset.prod_nonneg (fun i _ => hentry (σ i) i)
  · refine ⟨Equiv.refl n, Finset.mem_univ _, ?_⟩
    exact Finset.prod_pos (fun i _ => hdiag i)

/-- The strong row Gram bound is closed under finite block diagonal sums. -/
theorem strong_gram_blockDiagonal (A : ∀ i, Matrix (κ i) (κ i) ℝ)
    (hsize : ∀ i, 0 < Fintype.card (κ i))
    (hstrong : ∀ i, dimensionConstant (Fintype.card (κ i)) *
      (A i * (A i).transpose).permanent ≤ (A i).permanent ^ 2) :
    dimensionConstant (Fintype.card (Sigma κ)) *
      (Matrix.blockDiagonal' A * (Matrix.blockDiagonal' A).transpose).permanent ≤
        (Matrix.blockDiagonal' A).permanent ^ 2 := by
  rw [blockDiagonal_gram, permanent_blockDiagonal, permanent_blockDiagonal]
  have hnonneg : ∀ i, 0 ≤ (A i * (A i).transpose).permanent :=
    fun i => GyiresCirculant5.PermanentGram.permanent_gram_nonneg (A i)
  calc
    _ ≤ (∏ i, dimensionConstant (Fintype.card (κ i))) *
        ∏ i, (A i * (A i).transpose).permanent :=
      mul_le_mul_of_nonneg_right (dimensionConstant_card_sigma_le hsize)
        (Finset.prod_nonneg (fun i _ => hnonneg i))
    _ = ∏ i, dimensionConstant (Fintype.card (κ i)) *
        (A i * (A i).transpose).permanent := Finset.prod_mul_distrib.symm
    _ ≤ ∏ i, (A i).permanent ^ 2 := Finset.prod_le_prod₀
      (fun i _ => mul_nonneg (dimensionConstant_nonneg _) (hnonneg i))
      (fun i _ => hstrong i)
    _ = (∏ i, (A i).permanent) ^ 2 := Finset.prod_pow _ _ _

/-- With at least two nonempty stochastic blocks, the strong Gram bound is strict. -/
theorem strong_gram_blockDiagonal_lt (A : ∀ i, Matrix (κ i) (κ i) ℝ)
    (hsize : ∀ i, 0 < Fintype.card (κ i))
    (hblocks : 2 ≤ Fintype.card ι)
    (hA : ∀ i, A i ∈ doublyStochastic ℝ (κ i))
    (hstrong : ∀ i, dimensionConstant (Fintype.card (κ i)) *
      (A i * (A i).transpose).permanent ≤ (A i).permanent ^ 2) :
    dimensionConstant (Fintype.card (Sigma κ)) *
      (Matrix.blockDiagonal' A * (Matrix.blockDiagonal' A).transpose).permanent <
        (Matrix.blockDiagonal' A).permanent ^ 2 := by
  rw [blockDiagonal_gram, permanent_blockDiagonal, permanent_blockDiagonal]
  have hpos : ∀ i, 0 < (A i * (A i).transpose).permanent :=
    fun i => permanent_gram_pos_of_doublyStochastic (A i) (hA i)
  calc
    _ < (∏ i, dimensionConstant (Fintype.card (κ i))) *
        ∏ i, (A i * (A i).transpose).permanent :=
      mul_lt_mul_of_pos_right (dimensionConstant_card_sigma_lt hsize hblocks)
        (Finset.prod_pos (fun i _ => hpos i))
    _ = ∏ i, dimensionConstant (Fintype.card (κ i)) *
        (A i * (A i).transpose).permanent := Finset.prod_mul_distrib.symm
    _ ≤ ∏ i, (A i).permanent ^ 2 := Finset.prod_le_prod₀
      (fun i _ => mul_nonneg (dimensionConstant_nonneg _) (hpos i).le)
      (fun i _ => hstrong i)
    _ = (∏ i, (A i).permanent) ^ 2 := Finset.prod_pow _ _ _

/-- Both strong Gram bounds are closed under finite block diagonal sums. -/
theorem strong_bounds_blockDiagonal (A : ∀ i, Matrix (κ i) (κ i) ℝ)
    (hsize : ∀ i, 0 < Fintype.card (κ i))
    (hstrong : ∀ i,
      dimensionConstant (Fintype.card (κ i)) *
        (A i * (A i).transpose).permanent ≤ (A i).permanent ^ 2 ∧
      dimensionConstant (Fintype.card (κ i)) *
        ((A i).transpose * A i).permanent ≤ (A i).permanent ^ 2) :
    let B := Matrix.blockDiagonal' A
    dimensionConstant (Fintype.card (Sigma κ)) * (B * B.transpose).permanent ≤
        B.permanent ^ 2 ∧
      dimensionConstant (Fintype.card (Sigma κ)) * (B.transpose * B).permanent ≤
        B.permanent ^ 2 := by
  refine ⟨strong_gram_blockDiagonal A hsize (fun i => (hstrong i).1), ?_⟩
  have h := strong_gram_blockDiagonal (fun i => (A i).transpose) hsize
    (fun i => by simpa only [Matrix.transpose_transpose, Matrix.permanent_transpose]
      using (hstrong i).2)
  simpa only [← Matrix.blockDiagonal'_transpose, Matrix.transpose_transpose,
    Matrix.permanent_transpose] using h

/-- Both strong Gram bounds are strict when there are at least two stochastic blocks. -/
theorem strong_bounds_blockDiagonal_lt (A : ∀ i, Matrix (κ i) (κ i) ℝ)
    (hsize : ∀ i, 0 < Fintype.card (κ i))
    (hblocks : 2 ≤ Fintype.card ι)
    (hA : ∀ i, A i ∈ doublyStochastic ℝ (κ i))
    (hstrong : ∀ i,
      dimensionConstant (Fintype.card (κ i)) *
        (A i * (A i).transpose).permanent ≤ (A i).permanent ^ 2 ∧
      dimensionConstant (Fintype.card (κ i)) *
        ((A i).transpose * A i).permanent ≤ (A i).permanent ^ 2) :
    let B := Matrix.blockDiagonal' A
    dimensionConstant (Fintype.card (Sigma κ)) * (B * B.transpose).permanent <
        B.permanent ^ 2 ∧
      dimensionConstant (Fintype.card (Sigma κ)) * (B.transpose * B).permanent <
        B.permanent ^ 2 := by
  refine ⟨strong_gram_blockDiagonal_lt A hsize hblocks hA (fun i => (hstrong i).1), ?_⟩
  have h := strong_gram_blockDiagonal_lt (fun i => (A i).transpose) hsize hblocks
    (fun i => transpose_mem_doublyStochastic_iff.mpr (hA i))
    (fun i => by simpa only [Matrix.transpose_transpose, Matrix.permanent_transpose]
      using (hstrong i).2)
  simpa only [← Matrix.blockDiagonal'_transpose, Matrix.transpose_transpose,
    Matrix.permanent_transpose] using h

/-- Independent row and column permutations preserve stochastic block sums. -/
theorem blockDiagonal_submatrix_mem_doublyStochastic
    (A : ∀ i, Matrix (κ i) (κ i) ℝ)
    (σ τ : Equiv.Perm (Sigma κ))
    (hA : ∀ i, A i ∈ doublyStochastic ℝ (κ i)) :
    (Matrix.blockDiagonal' A).submatrix σ τ ∈ doublyStochastic ℝ (Sigma κ) := by
  exact reindex_mem_doublyStochastic (e₁ := σ.symm) (e₂ := τ.symm)
    (blockDiagonal_mem_doublyStochastic A hA)

/-- Both strong bounds hold after independent row and column permutations of a block sum. -/
theorem strong_bounds_blockDiagonal_submatrix_perm
    (A : ∀ i, Matrix (κ i) (κ i) ℝ)
    (σ τ : Equiv.Perm (Sigma κ))
    (hsize : ∀ i, 0 < Fintype.card (κ i))
    (hstrong : ∀ i,
      dimensionConstant (Fintype.card (κ i)) *
        (A i * (A i).transpose).permanent ≤ (A i).permanent ^ 2 ∧
      dimensionConstant (Fintype.card (κ i)) *
        ((A i).transpose * A i).permanent ≤ (A i).permanent ^ 2) :
    let B := (Matrix.blockDiagonal' A).submatrix σ τ
    dimensionConstant (Fintype.card (Sigma κ)) * (B * B.transpose).permanent ≤
        B.permanent ^ 2 ∧
      dimensionConstant (Fintype.card (Sigma κ)) * (B.transpose * B).permanent ≤
        B.permanent ^ 2 :=
  (strong_bounds_submatrix_perm_iff _ σ τ _).mpr
    (strong_bounds_blockDiagonal A hsize hstrong)

/-- The strict strong bounds hold after independent permutations of a stochastic block sum. -/
theorem strong_bounds_blockDiagonal_submatrix_perm_lt
    (A : ∀ i, Matrix (κ i) (κ i) ℝ)
    (σ τ : Equiv.Perm (Sigma κ))
    (hsize : ∀ i, 0 < Fintype.card (κ i))
    (hblocks : 2 ≤ Fintype.card ι)
    (hA : ∀ i, A i ∈ doublyStochastic ℝ (κ i))
    (hstrong : ∀ i,
      dimensionConstant (Fintype.card (κ i)) *
        (A i * (A i).transpose).permanent ≤ (A i).permanent ^ 2 ∧
      dimensionConstant (Fintype.card (κ i)) *
        ((A i).transpose * A i).permanent ≤ (A i).permanent ^ 2) :
    let B := (Matrix.blockDiagonal' A).submatrix σ τ
    dimensionConstant (Fintype.card (Sigma κ)) * (B * B.transpose).permanent <
        B.permanent ^ 2 ∧
      dimensionConstant (Fintype.card (Sigma κ)) * (B.transpose * B).permanent <
        B.permanent ^ 2 := by
  dsimp only
  rw [submatrix_perm_mul_transpose, transpose_mul_submatrix_perm]
  simp only [permanent_submatrix_perm]
  exact strong_bounds_blockDiagonal_lt A hsize hblocks hA hstrong

/-- Gyires's inequality holds for block sums and independent row and column permutations. -/
theorem gyires_blockDiagonal_submatrix_perm
    (A : ∀ i, Matrix (κ i) (κ i) ℝ)
    (σ τ : Equiv.Perm (Sigma κ))
    (hsize : ∀ i, 0 < Fintype.card (κ i))
    (hstrong : ∀ i,
      dimensionConstant (Fintype.card (κ i)) *
        (A i * (A i).transpose).permanent ≤ (A i).permanent ^ 2 ∧
      dimensionConstant (Fintype.card (κ i)) *
        ((A i).transpose * A i).permanent ≤ (A i).permanent ^ 2) :
    let B := (Matrix.blockDiagonal' A).submatrix σ τ
    dimensionConstant (Fintype.card (Sigma κ)) *
      ((B * B.transpose).permanent + (B.transpose * B).permanent +
        2 * (B * B).permanent) ≤ 4 * B.permanent ^ 2 := by
  have h := strong_bounds_blockDiagonal_submatrix_perm A σ τ hsize hstrong
  exact GyiresCirculant5.gyires_of_strong _ _ (dimensionConstant_nonneg _) h.1 h.2

/-- Gyires's inequality is strict for at least two stochastic blocks, including after permutations. -/
theorem gyires_blockDiagonal_submatrix_perm_lt
    (A : ∀ i, Matrix (κ i) (κ i) ℝ)
    (σ τ : Equiv.Perm (Sigma κ))
    (hsize : ∀ i, 0 < Fintype.card (κ i))
    (hblocks : 2 ≤ Fintype.card ι)
    (hA : ∀ i, A i ∈ doublyStochastic ℝ (κ i))
    (hstrong : ∀ i,
      dimensionConstant (Fintype.card (κ i)) *
        (A i * (A i).transpose).permanent ≤ (A i).permanent ^ 2 ∧
      dimensionConstant (Fintype.card (κ i)) *
        ((A i).transpose * A i).permanent ≤ (A i).permanent ^ 2) :
    let B := (Matrix.blockDiagonal' A).submatrix σ τ
    dimensionConstant (Fintype.card (Sigma κ)) *
      ((B * B.transpose).permanent + (B.transpose * B).permanent +
        2 * (B * B).permanent) < 4 * B.permanent ^ 2 := by
  have h := strong_bounds_blockDiagonal_submatrix_perm_lt A σ τ hsize hblocks hA hstrong
  exact GyiresCirculant5.PermanentGram.gyires_lt_of_strong _ _
    (dimensionConstant_nonneg _) h.1 h.2.le

end MathAndTheory.Gyires
