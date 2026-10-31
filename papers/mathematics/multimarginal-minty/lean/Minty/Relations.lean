import Minty.Core

namespace Minty

theorem compatible_iff_swaps (x y : Triple) :
    Compatible x y ↔ ∀ K : Finset (Fin 3),
      cost (mix K x y) + cost (mix K y x) ≤ cost x + cost y := by
  classical
  constructor
  · intro h K
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    dsimp [pairing, total] at h0 h1 h2
    by_cases k0 : (0 : Fin 3) ∈ K <;>
      by_cases k1 : (1 : Fin 3) ∈ K <;>
      by_cases k2 : (2 : Fin 3) ∈ K <;>
      simp [cost, pairing, mix, k0, k1, k2] <;> nlinarith
  · intro h i
    have hi := h {i}
    fin_cases i <;>
      simp [cost, pairing, mix] at hi <;>
      dsimp [pairing, total] <;> nlinarith

theorem cMonotone_iff_compatible (S : Set Triple) :
    CMonotone S ↔ ∀ x ∈ S, ∀ y ∈ S, Compatible x y := by
  constructor
  · intro h x hx y hy
    exact (compatible_iff_swaps x y).mpr (h x hx y hy)
  · intro h x hx y hy
    exact (compatible_iff_swaps x y).mp (h x hx y hy)

theorem cMonotone_mono {S T : Set Triple} (hT : CMonotone T) (hST : S ⊆ T) :
    CMonotone S := by
  intro x hx y hy K
  exact hT x (hST hx) y (hST hy) K

end Minty
