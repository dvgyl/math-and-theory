module

public import MatrixReindex
public import MathAndTheory.Mathematics.Gyires.DimensionConstant
public import Mathlib.Algebra.Group.End

@[expose] public section

namespace MathAndTheory.Gyires.PermutationAssembly

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


theorem permanent_nonneg_of_entries {α : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix α α ℝ) (hA : ∀ i j, 0 ≤ A i j) : 0 ≤ A.permanent := by
  exact Finset.sum_nonneg (fun σ _ => Finset.prod_nonneg (fun i _ => hA (σ i) i))

theorem strong_gram_blockDiagonal (A : ∀ i, Matrix (κ i) (κ i) ℝ)
    (hsize : ∀ i, 0 < Fintype.card (κ i))
    (hentry : ∀ i x y, 0 ≤ A i x y)
    (hstrong : ∀ i, dimensionConstant (Fintype.card (κ i)) *
      (A i * (A i).transpose).permanent ≤ (A i).permanent^2) :
    dimensionConstant (Fintype.card (Sigma κ)) *
      (Matrix.blockDiagonal' A * (Matrix.blockDiagonal' A).transpose).permanent ≤
      (Matrix.blockDiagonal' A).permanent^2 := by
  rw [Matrix.blockDiagonal'_transpose, ← Matrix.blockDiagonal'_mul,
    permanent_blockDiagonal, permanent_blockDiagonal]
  have hnonneg : ∀ i, 0 ≤ (A i * (A i).transpose).permanent := by
    intro i
    apply permanent_nonneg_of_entries
    intro x y
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (hentry i x k) (hentry i y k))
  calc
    _ ≤ (∏ i, dimensionConstant (Fintype.card (κ i))) *
        ∏ i, (A i * (A i).transpose).permanent :=
      mul_le_mul_of_nonneg_right (dimensionConstant_card_sigma_le hsize)
        (Finset.prod_nonneg (fun i _ => hnonneg i))
    _ = ∏ i, dimensionConstant (Fintype.card (κ i)) *
        (A i * (A i).transpose).permanent := Finset.prod_mul_distrib.symm
    _ ≤ ∏ i, (A i).permanent^2 := Finset.prod_le_prod₀
      (fun i _ => mul_nonneg (dimensionConstant_nonneg _) (hnonneg i))
      (fun i _ => hstrong i)
    _ = (∏ i, (A i).permanent)^2 := Finset.prod_pow _ _ _

end MathAndTheory.Gyires.PermutationAssembly
