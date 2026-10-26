module
public import MathAndTheory.Mathematics.QPermanent.GeneralIndex
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section

namespace MathAndTheory.QPermanent

open scoped BigOperators

def leftToRightCount (σ : Equiv.Perm (Fin 4)) : ℕ :=
  (Finset.univ.filter fun i : Fin 4 => i < 2 ∧ 2 ≤ σ i).card

def rightToLeftCount (σ : Equiv.Perm (Fin 4)) : ℕ :=
  (Finset.univ.filter fun i : Fin 4 => 2 ≤ i ∧ σ i < 2).card

theorem inversionCount_eq_sum {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    inversionCount σ = ∑ i : Fin n, ∑ j : Fin n,
      if i < j ∧ σ j < σ i then 1 else 0 := by
  rw [inversionCount, Finset.card_filter, Finset.sum_product]

theorem inversionCount_reindex {n : ℕ} {ι : Type*} [Fintype ι]
    (e : ι ≃ Fin n) (σ : Equiv.Perm (Fin n)) :
    inversionCount σ = ∑ i : ι, ∑ j : ι,
      if e i < e j ∧ σ (e j) < σ (e i) then 1 else 0 := by
  rw [inversionCount_eq_sum]
  symm
  calc
    _ = ∑ i : ι, ∑ j : Fin n,
        if e i < j ∧ σ j < σ (e i) then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact e.sum_comp (fun j => if e i < j ∧ σ j < σ (e i) then 1 else 0)
    _ = _ := e.sum_comp (fun i => ∑ j : Fin n,
      if i < j ∧ σ j < σ i then 1 else 0)

/-- Each inserted fixed middle coordinate contributes one inversion for each
active element crossing the cut between the first two and last two positions. -/
theorem inversionCount_liftCorePermutation (m : ℕ) (σ : Equiv.Perm (Fin 4)) :
    inversionCount (liftCorePermutation m σ) =
      inversionCount σ + m * (leftToRightCount σ + rightToLeftCount σ) := by
  rw [inversionCount_reindex (familyIndex m)]
  simp only [Fintype.sum_sum_type, liftCorePermutation_familyIndex,
    Equiv.Perm.sumCongr_apply, Sum.map_inl, Sum.map_inr, Equiv.refl_apply,
    familyIndex_inl_lt_inl, familyIndex_inl_lt_inr,
    familyIndex_inr_lt_inl, familyIndex_inr_lt_inr]
  simp only [Finset.sum_add_distrib]
  have hnone : ∀ i j : Fin m, ¬ (i < j ∧ j < i) := by
    intro i j h
    exact (lt_asymm h.1) h.2
  simp only [hnone, ite_false, Finset.sum_const_zero, add_zero]
  rw [← inversionCount_eq_sum]
  rw [leftToRightCount, rightToLeftCount, Finset.card_filter, Finset.card_filter]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_id, Finset.mul_sum, mul_add, add_assoc]

end MathAndTheory.QPermanent
