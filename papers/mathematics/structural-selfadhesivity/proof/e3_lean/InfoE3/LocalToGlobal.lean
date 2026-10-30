import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith

set_option Elab.async false

namespace InfoE3

variable {α : Type*} [DecidableEq α]

/-- Elementary diminishing-return squares on the Boolean lattice. -/
def LocalSquares (h : Finset α → ℤ) : Prop :=
  ∀ S i j, i ∉ S → j ∉ S → i ≠ j →
    h S + h (insert i (insert j S)) ≤ h (insert i S) + h (insert j S)

theorem LocalSquares.diminishing {h : Finset α → ℤ} (hs : LocalSquares h)
    (S T : Finset α) (hST : S ⊆ T) (i : α) (hi : i ∉ T) :
    h (insert i T) - h T ≤ h (insert i S) - h S := by
  induction T using Finset.strongInductionOn generalizing S with
  | _ T ih =>
    by_cases heq : S = T
    · subst S
      exact le_rfl
    have hss : S ⊂ T := Finset.ssubset_iff_subset_ne.mpr ⟨hST, heq⟩
    obtain ⟨j, hjT, hjS⟩ := Finset.exists_of_ssubset hss
    have hS0 : S ⊆ T.erase j := Finset.subset_erase.mpr ⟨hST, hjS⟩
    have hi0 : i ∉ T.erase j := fun hx => hi (Finset.mem_of_mem_erase hx)
    have hrec := ih (T.erase j) (Finset.erase_ssubset hjT) S hS0 hi0
    have hij : i ≠ j := by
      intro hh
      subst j
      exact hi hjT
    have hsq := hs (T.erase j) i j hi0 (by simp) hij
    rw [Finset.insert_erase hjT] at hsq
    linarith only [hrec, hsq]

/-- Full submodularity follows from the elementary squares, with no missing
subset pair or integrality approximation in the conclusion. -/
theorem LocalSquares.submodular {h : Finset α → ℤ} (hs : LocalSquares h)
    (A B : Finset α) : h (A ∩ B) + h (A ∪ B) ≤ h A + h B := by
  induction A using Finset.strongInductionOn with
  | _ A ih =>
    by_cases hAB : A ⊆ B
    · simp [Finset.inter_eq_left.mpr hAB, Finset.union_eq_right.mpr hAB]
    have hn : ∃ i ∈ A, i ∉ B := by
      by_contra hno
      apply hAB
      intro x hx
      by_contra hxb
      exact hno ⟨x, hx, hxb⟩
    obtain ⟨i, hiA, hiB⟩ := hn
    have hrec := ih (A.erase i) (Finset.erase_ssubset hiA)
    have hiU : i ∉ A.erase i ∪ B := by simp [hiB]
    have hdr := hs.diminishing (A.erase i) (A.erase i ∪ B)
      Finset.subset_union_left i hiU
    have hue : insert i (A.erase i ∪ B) = A ∪ B := by
      rw [← Finset.insert_union, Finset.insert_erase hiA]
    rw [hue, Finset.insert_erase hiA] at hdr
    have hiI : i ∉ A ∩ B := by simp [hiB]
    rw [Finset.erase_inter, Finset.erase_eq_of_notMem hiI] at hrec
    linarith only [hrec, hdr]

theorem monotone_of_singleton_steps {h : Finset α → ℤ}
    (hs : ∀ S i, i ∉ S → h S ≤ h (insert i S))
    (A B : Finset α) (hAB : A ⊆ B) : h A ≤ h B := by
  induction B using Finset.strongInductionOn generalizing A with
  | _ B ih =>
    by_cases heq : A = B
    · subst A
      exact le_rfl
    have hss : A ⊂ B := Finset.ssubset_iff_subset_ne.mpr ⟨hAB, heq⟩
    obtain ⟨i, hiB, hiA⟩ := Finset.exists_of_ssubset hss
    have hA0 : A ⊆ B.erase i := Finset.subset_erase.mpr ⟨hAB, hiA⟩
    have hrec := ih (B.erase i) (Finset.erase_ssubset hiB) A hA0
    have hstep := hs (B.erase i) i (by simp)
    rw [Finset.insert_erase hiB] at hstep
    exact hrec.trans hstep

end InfoE3
