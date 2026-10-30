import BinarySpectral
import BinaryAperiodic
import BinaryNoSubspace

set_option autoImplicit false
namespace BinaryFuglede

theorem explicit_no_periodic_complement (B : Set V)
    (ht : TilingPair Eset B) : ¬ Periodic B := by
  classical
  letI : Fintype Eset := Fintype.ofFinite Eset
  letI : Fintype B := Fintype.ofFinite B
  exact not_periodic_complement B card_Eset ht

theorem explicit_no_subspace_complement (H : Submodule (ZMod 2) V) :
    ¬ TilingPair Eset (H : Set V) := by
  classical
  letI : Fintype Eset := Fintype.ofFinite Eset
  exact no_subspace_tiling_of_card card_Eset H

/-- The actual nine-dimensional elementary abelian group fails the PT property. -/
theorem binary_nine_fails_PT : ¬ HasPTProperty := by
  intro h
  rcases h Eset Tset explicit_tiling with hper | ⟨B, ht, hper⟩
  · exact Eset_not_periodic hper
  · exact explicit_no_periodic_complement B ht hper

/-- The complete explicit result, including the actual spectral basis and all
complements. No enumeration-completeness or numerical hypothesis remains. -/
theorem spectral_aperiodic_tile_without_periodic_complement
    [Fintype Eset] [Fintype Lset] [Fintype Tset] :
    Fintype.card Eset = 64 ∧ Fintype.card Lset = 64 ∧ Fintype.card Tset = 8 ∧
    IsSpectral Eset ∧ TilingPair Eset Tset ∧ ¬ Periodic Eset ∧
    (∀ B : Set V, TilingPair Eset B → ¬ Periodic B) ∧
    (∀ H : Submodule (ZMod 2) V, ¬ TilingPair Eset (H : Set V)) := by
  exact ⟨card_Eset, card_Lset, card_Tset, Eset_isSpectral, explicit_tiling,
    Eset_not_periodic, explicit_no_periodic_complement, explicit_no_subspace_complement⟩

/-- A counterexample to the universal linear-subspace-complement assertion for
64-point spectral sets in the actual vector space F₂⁹. -/
theorem exists_spectral_counterexample :
    ∃ A : Set V, ∃ hA : Fintype A,
      @Fintype.card A hA = 64 ∧ @IsSpectral A hA ∧
      (∃ B : Set V, TilingPair A B) ∧
      (∀ H : Submodule (ZMod 2) V, ¬ TilingPair A (H : Set V)) := by
  classical
  letI : Fintype Eset := Fintype.ofFinite Eset
  exact ⟨Eset, inferInstance, card_Eset, Eset_isSpectral,
    ⟨Tset, explicit_tiling⟩, explicit_no_subspace_complement⟩

end BinaryFuglede
