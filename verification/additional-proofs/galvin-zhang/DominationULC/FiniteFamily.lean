import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega

/-!
# The deletion double count for upward-closed finite set families

The deletion count below counts actual pairs consisting of a member of the
family and one of its elements whose removal stays in the family.
-/

namespace DominationULC

open scoped BigOperators

variable {V : Type*} [Fintype V]

def UpwardClosed (F : Finset V → Prop) : Prop :=
  ∀ ⦃s t⦄, s ⊆ t → F s → F t

noncomputable def familyRank (F : Finset V → Prop) (k : ℕ) : Finset (Finset V) := by
  classical
  exact Finset.univ.filter (fun s => s.card = k ∧ F s)

noncomputable def familyRankCount (F : Finset V → Prop) (k : ℕ) : ℕ :=
  (familyRank F k).card

noncomputable def deletionCount (F : Finset V → Prop) (k : ℕ) : ℕ := by
  classical
  exact ∑ s ∈ familyRank F k, (s.filter (fun v => F (s.erase v))).card

@[simp] theorem mem_familyRank (F : Finset V → Prop) (k : ℕ) (s : Finset V) :
    s ∈ familyRank F k ↔ s.card = k ∧ F s := by
  classical
  simp [familyRank]

/-- Erasing the marked element and inserting the marked missing element are
inverse maps between successful deletions and extensions of a lower-rank set. -/
theorem deletionCount_succ (F : Finset V → Prop) (hF : UpwardClosed F) (k : ℕ) :
    deletionCount F (k + 1) = (Fintype.card V - k) * familyRankCount F k := by
  classical
  let D := (familyRank F (k + 1)).sigma
    (fun s => s.filter (fun v => F (s.erase v)))
  let E := (familyRank F k).sigma (fun s => (Finset.univ : Finset V) \ s)
  have hDE : D.card = E.card := by
    apply Finset.card_nbij'
      (fun p : (s : Finset V) × V => ⟨p.1.erase p.2, p.2⟩)
      (fun p : (s : Finset V) × V => ⟨insert p.2 p.1, p.2⟩)
    · intro p hp
      rcases Finset.mem_sigma.mp hp with ⟨hp₁, hp₂⟩
      rcases (mem_familyRank F (k + 1) p.1).mp hp₁ with ⟨hc, hs⟩
      rcases Finset.mem_filter.mp hp₂ with ⟨hv, he⟩
      apply Finset.mem_sigma.mpr
      constructor
      · apply (mem_familyRank F k (p.1.erase p.2)).mpr
        exact ⟨by rw [Finset.card_erase_of_mem hv, hc]; omega, he⟩
      · simp
    · intro p hp
      rcases Finset.mem_sigma.mp hp with ⟨hp₁, hp₂⟩
      rcases (mem_familyRank F k p.1).mp hp₁ with ⟨hc, hs⟩
      have hv : p.2 ∉ p.1 := (Finset.mem_sdiff.mp hp₂).2
      apply Finset.mem_sigma.mpr
      constructor
      · apply (mem_familyRank F (k + 1) (insert p.2 p.1)).mpr
        exact ⟨by rw [Finset.card_insert_of_not_mem hv, hc],
          hF (Finset.subset_insert _ _) hs⟩
      · simp [Finset.erase_insert hv, hs]
    · intro p hp
      have hv : p.2 ∈ p.1 := (Finset.mem_filter.mp (Finset.mem_sigma.mp hp).2).1
      simp [Finset.insert_erase hv]
    · intro p hp
      have hv : p.2 ∉ p.1 := (Finset.mem_sdiff.mp (Finset.mem_sigma.mp hp).2).2
      simp [Finset.erase_insert hv]
  calc
    deletionCount F (k + 1) = D.card := by
      simp [deletionCount, D, Finset.card_sigma]
    _ = E.card := hDE
    _ = (Fintype.card V - k) * familyRankCount F k := by
      rw [Finset.card_sigma]
      calc
        (∑ s ∈ familyRank F k, ((Finset.univ : Finset V) \ s).card) =
            ∑ s ∈ familyRank F k, (Fintype.card V - k) := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [Finset.card_sdiff (Finset.subset_univ s), Finset.card_univ,
            ((mem_familyRank F k s).mp hs).1]
        _ = _ := by simp [familyRankCount, Nat.mul_comm]

theorem familyRankCount_pos_iff (F : Finset V → Prop) (k : ℕ) :
    0 < familyRankCount F k ↔ ∃ s : Finset V, s.card = k ∧ F s := by
  classical
  simp [familyRankCount, Finset.card_pos, Finset.Nonempty]

theorem familyRankCount_pos_mono (F : Finset V → Prop) (hF : UpwardClosed F)
    {k j : ℕ} (hk : 0 < familyRankCount F k) (hkj : k ≤ j)
    (hj : j ≤ Fintype.card V) : 0 < familyRankCount F j := by
  classical
  obtain ⟨s, hs, hFs⟩ := (familyRankCount_pos_iff F k).mp hk
  obtain ⟨t, hst, ht⟩ := Finset.exists_superset_card_eq (by omega : s.card ≤ j) hj
  exact (familyRankCount_pos_iff F j).mpr ⟨t, ht, hF hst hFs⟩

theorem deletionCount_le (F : Finset V → Prop) (k : ℕ) :
    deletionCount F k ≤ k * familyRankCount F k := by
  classical
  calc
    deletionCount F k ≤ ∑ s ∈ familyRank F k, k := by
      apply Finset.sum_le_sum
      intro s hs
      exact (Finset.card_filter_le _ _).trans_eq ((mem_familyRank F k s).mp hs).1
    _ = _ := by simp [familyRankCount, Nat.mul_comm]

end DominationULC
