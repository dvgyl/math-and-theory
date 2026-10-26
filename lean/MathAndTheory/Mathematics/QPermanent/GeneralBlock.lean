module
public import MathAndTheory.Mathematics.QPermanent.GeneralPositivity
public import Mathlib.GroupTheory.Perm.Finite

@[expose] public section

open scoped BigOperators

namespace MathAndTheory.QPermanent

/-- A permutation fixing the entire second summand comes from the first summand. -/
theorem perm_eq_sumCongr_of_fix_right {ι κ : Type*} [Fintype ι] [Fintype κ]
    (τ : Equiv.Perm (ι ⊕ κ)) (hfix : ∀ j : κ, τ (Sum.inr j) = Sum.inr j) :
    ∃ σ : Equiv.Perm ι, Equiv.sumCongr σ (Equiv.refl κ) = τ := by
  have hr : Set.MapsTo τ (Set.range Sum.inr) (Set.range Sum.inr) := by
    rintro _ ⟨j, rfl⟩
    exact ⟨j, (hfix j).symm⟩
  have hl := (Equiv.Perm.perm_mapsTo_inl_iff_mapsTo_inr τ).mpr hr
  obtain ⟨⟨σ, ρ⟩, hσρ⟩ :=
    (MonoidHom.mem_range).mp (Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hl)
  have hρ : ρ = Equiv.refl κ := by
    ext j
    apply (Sum.inr_injective (α := ι))
    have h := congrArg (fun p : Equiv.Perm (ι ⊕ κ) => p (Sum.inr j)) hσρ
    simpa [Equiv.Perm.sumCongrHom_apply, hfix] using h
  exact ⟨σ, by simpa [Equiv.Perm.sumCongrHom_apply, hρ] using hσρ⟩

/-- An arbitrary weight is permitted: this reduction does not presume anything
about inversions or the polynomial we aim to establish. -/
theorem weighted_perm_sum_identity_block {ι κ R : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] [CommSemiring R]
    (A : Matrix ι ι R) (w : Equiv.Perm (ι ⊕ κ) → R) :
    (∑ τ : Equiv.Perm (ι ⊕ κ), w τ *
      ∏ i : ι ⊕ κ, Matrix.fromBlocks A 0 0 (1 : Matrix κ κ R) i (τ i)) =
    ∑ σ : Equiv.Perm ι, w (Equiv.sumCongr σ (Equiv.refl κ)) * ∏ i : ι, A i (σ i) := by
  classical
  let e : Equiv.Perm ι ↪ Equiv.Perm (ι ⊕ κ) :=
    ⟨fun σ => Equiv.sumCongr σ (Equiv.refl κ), by
      intro σ ρ h
      ext i
      apply (Sum.inl_injective (β := κ))
      simpa using congrArg (fun p : Equiv.Perm (ι ⊕ κ) => p (Sum.inl i)) h⟩
  let S := Finset.univ.map e
  have hs : ∀ τ ∈ (Finset.univ : Finset (Equiv.Perm (ι ⊕ κ))), τ ∉ S →
      w τ * ∏ i : ι ⊕ κ, Matrix.fromBlocks A 0 0 (1 : Matrix κ κ R) i (τ i) = 0 := by
    intro τ _ hτ
    suffices hp : (∏ i : ι ⊕ κ,
      Matrix.fromBlocks A 0 0 (1 : Matrix κ κ R) i (τ i)) = 0 by simp [hp]
    by_contra hp
    have hfix : ∀ j : κ, τ (Sum.inr j) = Sum.inr j := by
      intro j
      by_contra hj
      have hz : Matrix.fromBlocks A 0 0 (1 : Matrix κ κ R)
          (Sum.inr j) (τ (Sum.inr j)) = 0 := by
        cases hval : τ (Sum.inr j) with
        | inl i => simp [Matrix.fromBlocks]
        | inr k =>
          have hjk : j ≠ k := by
            intro h
            subst k
            exact hj hval
          simp [Matrix.fromBlocks, Matrix.one_apply, hjk]
      exact hp (Finset.prod_eq_zero (Finset.mem_univ (Sum.inr j)) hz)
    obtain ⟨σ, hσ⟩ := perm_eq_sumCongr_of_fix_right τ hfix
    apply hτ
    exact Finset.mem_map.mpr ⟨σ, Finset.mem_univ _, hσ⟩
  calc
    _ = ∑ τ ∈ S, w τ *
        ∏ i : ι ⊕ κ, Matrix.fromBlocks A 0 0 (1 : Matrix κ κ R) i (τ i) :=
      (Finset.sum_subset (Finset.subset_univ S) hs).symm
    _ = _ := by
      simp only [S, Finset.sum_map]
      apply Finset.sum_congr rfl
      intro σ _
      change w (Equiv.sumCongr σ (Equiv.refl κ)) *
        (∏ i : ι ⊕ κ, Matrix.fromBlocks A 0 0 (1 : Matrix κ κ R)
          i (Equiv.sumCongr σ (Equiv.refl κ) i)) = _
      simp [Fintype.prod_sum_type, Matrix.fromBlocks, Matrix.one_apply]

theorem weighted_perm_sum_reindex {ι κ R : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] [CommSemiring R]
    (e : ι ≃ κ) (A : Matrix ι ι R) (w : Equiv.Perm κ → R) :
    (∑ τ : Equiv.Perm κ, w τ * ∏ i : κ, A (e.symm i) (e.symm (τ i))) =
    ∑ σ : Equiv.Perm ι, w (e.permCongr σ) * ∏ i : ι, A i (σ i) := by
  classical
  rw [← (e.permCongr).sum_comp]
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  have h := e.prod_comp (fun i : κ => A (e.symm i) (e.symm ((e.permCongr σ) i)))
  simpa [Equiv.permCongr_apply] using h.symm

/-- Reduction of the genuine q-permanent to its four active coordinates. -/
theorem qPermanent_family_reduction (m : ℕ) (a d q : ℝ) :
    qPermanent (familyMatrix m a d) q =
      ∑ σ : Equiv.Perm (Fin 4), q ^ inversionCount (liftCorePermutation m σ) *
        ∏ i : Fin 4, familyCore a d i (σ i) := by
  classical
  unfold qPermanent familyMatrix
  change (∑ τ : Equiv.Perm (Fin (m + 4)), q ^ inversionCount τ *
      ∏ i : Fin (m + 4),
        Matrix.fromBlocks (familyCore a d) 0 0 (1 : Matrix (Fin m) (Fin m) ℝ)
          ((familyIndex m).symm i) ((familyIndex m).symm (τ i))) = _
  rw [weighted_perm_sum_reindex (familyIndex m)]
  exact weighted_perm_sum_identity_block (familyCore a d)
    (fun τ => q ^ inversionCount ((familyIndex m).permCongr τ))

end MathAndTheory.QPermanent
