module
public import MathAndTheory.Mathematics.QPermanent.Definitions
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace MathAndTheory.QPermanent

/-- Reinsert `m` middle coordinates between the two halves of `Fin 4`. -/
def familyIndex (m : ℕ) : (Fin 4 ⊕ Fin m) ≃ Fin (m + 4) :=
  (Equiv.sumCongr (finSumFinEquiv (m := 2) (n := 2)).symm (Equiv.refl (Fin m))).trans
    ((Equiv.sumAssoc (Fin 2) (Fin 2) (Fin m)).trans
      ((Equiv.sumCongr (Equiv.refl (Fin 2)) (Equiv.sumComm (Fin 2) (Fin m))).trans
        ((Equiv.sumCongr (Equiv.refl (Fin 2)) (finSumFinEquiv (m := m) (n := 2))).trans
          ((finSumFinEquiv (m := 2) (n := m + 2)).trans (finCongr (by omega))))))

def liftCorePermutation (m : ℕ) (σ : Equiv.Perm (Fin 4)) :
    Equiv.Perm (Fin (m + 4)) :=
  (familyIndex m).permCongr (Equiv.sumCongr σ (Equiv.refl (Fin m)))

@[simp] theorem liftCorePermutation_familyIndex (m : ℕ) (σ : Equiv.Perm (Fin 4))
    (x : Fin 4 ⊕ Fin m) :
    liftCorePermutation m σ (familyIndex m x) =
      familyIndex m (Equiv.sumCongr σ (Equiv.refl (Fin m)) x) := by
  simp [liftCorePermutation]

theorem familyIndex_inl_val (m : ℕ) (i : Fin 4) :
    (familyIndex m (.inl i)).val = if i.val < 2 then i.val else m + i.val := by
  fin_cases i <;>
    simp [familyIndex, finSumFinEquiv, Fin.addCases]

@[simp] theorem familyIndex_inr_val (m : ℕ) (i : Fin m) :
    (familyIndex m (.inr i)).val = i.val + 2 := by
  simp [familyIndex, finSumFinEquiv]

@[simp] theorem familyIndex_inl_lt_inl (m : ℕ) (i j : Fin 4) :
    familyIndex m (.inl i) < familyIndex m (.inl j) ↔ i < j := by
  change (familyIndex m (.inl i)).val < (familyIndex m (.inl j)).val ↔ i.val < j.val
  rw [familyIndex_inl_val, familyIndex_inl_val]
  split_ifs <;> omega

@[simp] theorem familyIndex_inl_lt_inr (m : ℕ) (i : Fin 4) (j : Fin m) :
    familyIndex m (.inl i) < familyIndex m (.inr j) ↔ i < 2 := by
  change (familyIndex m (.inl i)).val < (familyIndex m (.inr j)).val ↔ i.val < 2
  rw [familyIndex_inl_val, familyIndex_inr_val]
  have hj := j.isLt
  split_ifs <;> omega

@[simp] theorem familyIndex_inr_lt_inl (m : ℕ) (i : Fin m) (j : Fin 4) :
    familyIndex m (.inr i) < familyIndex m (.inl j) ↔ 2 ≤ j := by
  change (familyIndex m (.inr i)).val < (familyIndex m (.inl j)).val ↔ 2 ≤ j.val
  rw [familyIndex_inr_val, familyIndex_inl_val]
  have hi := i.isLt
  split_ifs <;> omega

@[simp] theorem familyIndex_inr_lt_inr (m : ℕ) (i j : Fin m) :
    familyIndex m (.inr i) < familyIndex m (.inr j) ↔ i < j := by
  change (familyIndex m (.inr i)).val < (familyIndex m (.inr j)).val ↔ i.val < j.val
  rw [familyIndex_inr_val, familyIndex_inr_val]
  omega

end MathAndTheory.QPermanent
