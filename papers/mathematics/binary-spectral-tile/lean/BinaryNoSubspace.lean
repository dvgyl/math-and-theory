import BinaryPeriodicity

set_option autoImplicit false
namespace BinaryFuglede

lemma no_subspace_tiling_of_card [Fintype Eset] (hEcard : Fintype.card Eset = 64)
    (H : Submodule (ZMod 2) V) : ¬ TilingPair Eset (H : Set V) := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  intro ht
  have hc : Fintype.card H = 8 := complement_card_eight (H : Set V) hEcard ht
  have hp : (2 : ℕ) ^ Module.finrank (ZMod 2) H = 8 := by
    simpa only [ZMod.card, hc] using
      (Module.card_eq_pow_finrank (K := ZMod 2) (V := H)).symm
  have hfin : Module.finrank (ZMod 2) H = 3 :=
    Nat.pow_right_injective (by decide) hp
  exact no_three_dimensional_tiling H hfin ht

end BinaryFuglede
