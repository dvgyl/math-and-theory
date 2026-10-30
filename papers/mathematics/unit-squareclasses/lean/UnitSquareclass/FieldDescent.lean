import Mathlib

/-!
# Finite-subfield descent for algebraic totally real fields

Every complex embedding of an intermediate field extends to the ambient algebraic
field. Consequently total reality and total positivity descend. A finite set of
algebraic elements is contained in a finite number field.
-/

noncomputable section

namespace UnitSquareclass

variable {K : Type*} [Field K] [CharZero K] [Algebra.IsAlgebraic ℚ K]

/-- A complex embedding of an intermediate field extends to the ambient
algebraic extension of the rationals. No finiteness hypothesis on `K` is used. -/
theorem extend_complex_embedding (F : IntermediateField ℚ K) (φ : F →+* ℂ) :
    ∃ ψ : K →+* ℂ, ∀ x : F, ψ (x : K) = φ x := by
  obtain ⟨ψ, hψ⟩ :=
    IsAlgClosed.surjective_restrictDomain_of_isAlgebraic
      (K := ℚ) (L := F) (M := ℂ) (E := K) φ.toRatAlgHom
  refine ⟨ψ.toRingHom, ?_⟩
  intro x
  exact congrArg (fun f : F →ₐ[ℚ] ℂ => f x) hψ

/-- Total reality, expressed for every complex embedding, descends to any
intermediate field. -/
theorem totally_real_intermediate (F : IntermediateField ℚ K)
    (hr : ∀ (ψ : K →+* ℂ) (a : K), (ψ a).im = 0) :
    ∀ (φ : F →+* ℂ) (a : F), (φ a).im = 0 := by
  intro φ a
  obtain ⟨ψ, hψ⟩ := extend_complex_embedding F φ
  rw [← hψ a]
  exact hr ψ (a : K)

/-- Total positivity descends because all complex embeddings extend. -/
theorem positive_intermediate (F : IntermediateField ℚ K) (a : F)
    (hp : ∀ ψ : K →+* ℂ, 0 < (ψ (a : K)).re) :
    ∀ φ : F →+* ℂ, 0 < (φ a).re := by
  intro φ
  obtain ⟨ψ, hψ⟩ := extend_complex_embedding F φ
  rw [← hψ a]
  exact hp ψ

/-- Any finite collection of elements of an algebraic extension of the
rationals belongs to a finite number field inside it. -/
theorem exists_numberField_containing (S : Finset K) :
    ∃ F : IntermediateField ℚ K, NumberField F ∧ ∀ x ∈ S, x ∈ F := by
  let F : IntermediateField ℚ K := IntermediateField.adjoin ℚ (S : Set K)
  haveI : FiniteDimensional ℚ F :=
    IntermediateField.finiteDimensional_adjoin
      (fun x _ => Algebra.IsIntegral.isIntegral x)
  refine ⟨F, { to_charZero := inferInstance, to_finiteDimensional := inferInstance }, ?_⟩
  intro x hx
  exact IntermediateField.subset_adjoin ℚ (S : Set K) hx

omit [Algebra.IsAlgebraic ℚ K] in
/-- Integrality over the integers is unchanged on passing to an intermediate
field containing the element. -/
theorem isIntegral_intermediate_iff (F : IntermediateField ℚ K) (a : F) :
    IsIntegral ℤ (a : K) ↔ IsIntegral ℤ a := by
  exact isIntegral_algHom_iff F.val.toRingHom.toIntAlgHom Subtype.val_injective

end UnitSquareclass

#print axioms UnitSquareclass.extend_complex_embedding
#print axioms UnitSquareclass.totally_real_intermediate
#print axioms UnitSquareclass.positive_intermediate
#print axioms UnitSquareclass.exists_numberField_containing
#print axioms UnitSquareclass.isIntegral_intermediate_iff
