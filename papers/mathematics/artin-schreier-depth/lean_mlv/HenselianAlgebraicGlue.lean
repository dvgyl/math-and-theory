import Mathlib

/-!
# Gluing the finite rational extensions

This is a reduction from finite field extensions to arbitrary algebraic
extensions. All valuation axioms are proved for the glued function. The
finite existence and uniqueness inputs must be supplied by the standard
henselian bridge; they are not treated as a new definition of henselianity.
-/

noncomputable section

namespace NTCThird

open IntermediateField

/-- Coherent finite rational extensions glue to an actual valuation on an
arbitrary algebraic extension, with exact restriction to the base. -/
theorem exists_rationalAddValuation_of_finite_extensions
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsAlgebraic F E]
    (vF : AddValuation F (WithTop ℚ))
    (hexists : ∀ S : IntermediateField F E, FiniteDimensional F S →
      ∃ vS : AddValuation S (WithTop ℚ),
        ∀ a : F, vS (algebraMap F S a) = vF a)
    (hunique : ∀ S : IntermediateField F E, FiniteDimensional F S →
      ∀ v₁ v₂ : AddValuation S (WithTop ℚ),
        (∀ a : F, v₁ (algebraMap F S a) = vF a) →
        (∀ a : F, v₂ (algebraMap F S a) = vF a) → v₁ = v₂) :
    ∃ vE : AddValuation E (WithTop ℚ),
      ∀ a : F, vE (algebraMap F E a) = vF a := by
  classical
  choose family family_extends using hexists
  have hsingle (x : E) : FiniteDimensional F F⟮x⟯ :=
    IntermediateField.adjoin.finiteDimensional
      (Algebra.IsAlgebraic.isAlgebraic (R := F) x).isIntegral
  let value : E → WithTop ℚ := fun x =>
    family F⟮x⟯ (hsingle x) (AdjoinSimple.gen F x)
  have hcompatible (S : IntermediateField F E) (hS : FiniteDimensional F S)
      (x : S) : value (x : E) = family S hS x := by
    let T : IntermediateField F E := F⟮(x : E)⟯
    have hTS : T ≤ S := IntermediateField.adjoin_simple_le_iff.mpr x.property
    let ι : T →ₐ[F] S := IntermediateField.inclusion hTS
    have hext : ∀ a : F,
        ((family S hS).comap ι.toRingHom) (algebraMap F T a) = vF a := by
      intro a
      change family S hS (ι (algebraMap F T a)) = vF a
      rw [ι.commutes]
      exact family_extends S hS a
    have heq : family T (hsingle (x : E)) =
        (family S hS).comap ι.toRingHom :=
      hunique T (hsingle (x : E)) _ _ (family_extends T (hsingle (x : E))) hext
    change family T (hsingle (x : E)) (AdjoinSimple.gen F (x : E)) =
      family S hS x
    rw [heq]
    rfl
  have hpair (x y : E) :
      FiniteDimensional F (IntermediateField.adjoin F ({x, y} : Set E)) :=
    IntermediateField.finiteDimensional_adjoin
      (fun z _ => (Algebra.IsAlgebraic.isAlgebraic (R := F) z).isIntegral)
  have hzero : value 0 = ⊤ := by
    change family F⟮(0 : E)⟯ (hsingle 0) (0 : F⟮(0 : E)⟯) = ⊤
    exact AddValuation.map_zero _
  have hone : value 1 = 0 := by
    change family F⟮(1 : E)⟯ (hsingle 1) (1 : F⟮(1 : E)⟯) = 0
    exact AddValuation.map_one _
  have hadd (x y : E) : min (value x) (value y) ≤ value (x + y) := by
    let S := IntermediateField.adjoin F ({x, y} : Set E)
    let xS : S := ⟨x, IntermediateField.subset_adjoin F _ (by simp)⟩
    let yS : S := ⟨y, IntermediateField.subset_adjoin F _ (by simp)⟩
    have hx := hcompatible S (hpair x y) xS
    have hy := hcompatible S (hpair x y) yS
    have hxy := hcompatible S (hpair x y) (xS + yS)
    change value (x + y) = _ at hxy
    rw [hx, hy, hxy]
    exact (family S (hpair x y)).map_add xS yS
  have hmul (x y : E) : value (x * y) = value x + value y := by
    let S := IntermediateField.adjoin F ({x, y} : Set E)
    let xS : S := ⟨x, IntermediateField.subset_adjoin F _ (by simp)⟩
    let yS : S := ⟨y, IntermediateField.subset_adjoin F _ (by simp)⟩
    have hx := hcompatible S (hpair x y) xS
    have hy := hcompatible S (hpair x y) yS
    have hxy := hcompatible S (hpair x y) (xS * yS)
    change value (x * y) = _ at hxy
    rw [hx, hy, hxy]
    exact (family S (hpair x y)).map_mul xS yS
  refine ⟨AddValuation.of value hzero hone hadd hmul, ?_⟩
  intro a
  change family F⟮algebraMap F E a⟯ (hsingle (algebraMap F E a))
    (algebraMap F F⟮algebraMap F E a⟯ a) = vF a
  exact family_extends _ _ a

end NTCThird

