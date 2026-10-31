import Minty.Relations

namespace Minty

theorem cMonotone_sUnion {C : Set (Set Triple)}
    (hC : ∀ S ∈ C, CMonotone S) (hchain : IsChain (· ⊆ ·) C) :
    CMonotone (⋃₀ C) := by
  intro x hx y hy K
  obtain ⟨S, hSC, hxS⟩ := hx
  obtain ⟨T, hTC, hyT⟩ := hy
  by_cases hST : S = T
  · subst T
    exact hC S hSC x hxS y hyT K
  · rcases hchain hSC hTC hST with h | h
    · exact hC T hTC x (h hxS) y hyT K
    · exact hC S hSC x hxS y (h hyT) K

theorem exists_maximal_extension (S : Set Triple) (hS : CMonotone S) :
    ∃ T : Set Triple, S ⊆ T ∧ MaximalCMonotone T := by
  classical
  let family : Set (Set Triple) := {T | S ⊆ T ∧ CMonotone T}
  have hchain : ∀ C ⊆ family, IsChain (· ⊆ ·) C → C.Nonempty →
      ∃ U ∈ family, ∀ T ∈ C, T ⊆ U := by
    intro C hCF hC hne
    obtain ⟨T, hTC⟩ := hne
    refine ⟨⋃₀ C, ⟨?_, ?_⟩, ?_⟩
    · exact (hCF hTC).1.trans (Set.subset_sUnion_of_mem hTC)
    · exact cMonotone_sUnion (fun U hU => (hCF hU).2) hC
    · intro U hU
      exact Set.subset_sUnion_of_mem hU
  obtain ⟨T, hST, hmax⟩ :=
    zorn_subset_nonempty family hchain S ⟨Set.Subset.rfl, hS⟩
  refine ⟨T, hST, hmax.prop.2, ?_⟩
  intro U hU hTU
  exact (hmax.eq_of_subset ⟨hST.trans hTU, hU⟩ hTU).symm

end Minty
