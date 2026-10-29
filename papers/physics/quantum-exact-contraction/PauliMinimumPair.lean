import PauliChannel
import Mathlib.Data.Finset.Max

/-! Two smallest entries of a four-element real family, with ties retained. -/

namespace PauliMinimumPair
noncomputable section

theorem exists_minimal_pair (w : Fin 4 → ℝ) :
    ∃ a b : Fin 4, a ≠ b ∧ (∀ i, w a ≤ w i) ∧
      (∀ i, i ≠ a → w b ≤ w i) := by
  obtain ⟨a, _, ha⟩ := Finset.exists_min_image Finset.univ w
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin 4)).Nonempty)
  have hn : (Finset.univ.erase a : Finset (Fin 4)).Nonempty := by
    obtain ⟨c,hc⟩ := exists_ne a
    exact ⟨c,Finset.mem_erase.mpr ⟨hc,Finset.mem_univ c⟩⟩
  obtain ⟨b,hb,hmin⟩ := Finset.exists_min_image (Finset.univ.erase a) w hn
  refine ⟨a,b,(Finset.mem_erase.mp hb).1.symm,?_,?_⟩
  · intro i
    exact ha i (Finset.mem_univ i)
  · intro i hia
    exact hmin i (Finset.mem_erase.mpr ⟨hia,Finset.mem_univ i⟩)

end
end PauliMinimumPair
