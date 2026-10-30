module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Tactic.Abel

@[expose] public section

namespace MatCP1Converse

variable {F V W Z : Type*} [Field F]
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
  [AddCommGroup Z] [Module F Z]

/-- A linear map factors through any other linear map with smaller kernel, after
extending the resulting map from its range to its entire codomain. -/
theorem exists_factor_of_ker_le (f : W →ₗ[F] V) (g : W →ₗ[F] Z)
    (h : LinearMap.ker f ≤ LinearMap.ker g) :
    ∃ d : V →ₗ[F] Z, d.comp f = g := by
  classical
  let k : LinearMap.range f →ₗ[F] Z :=
    ((LinearMap.ker f).liftQ g h).comp f.quotKerEquivRange.symm.toLinearMap
  obtain ⟨d, hd⟩ := k.exists_extend
  refine ⟨d, ?_⟩
  apply LinearMap.ext
  intro w
  have hw := LinearMap.congr_fun hd ⟨f w, LinearMap.mem_range_self f w⟩
  simpa [k] using hw

/-- Two embeddings into the same finite-dimensional space are conjugate by an
ambient linear automorphism. -/
theorem exists_automorphism_map_embeddings [FiniteDimensional F V]
    (X0 X1 : W →ₗ[F] V) (h0 : Function.Injective X0) (h1 : Function.Injective X1) :
    ∃ T : V ≃ₗ[F] V, ∀ w, T (X0 w) = X1 w := by
  classical
  let e0 := LinearEquiv.ofInjective X0 h0
  let e1 := LinearEquiv.ofInjective X1 h1
  obtain ⟨T, hT⟩ := Submodule.exists_linearEquiv_restrict_eq (e0.symm.trans e1)
  refine ⟨T, ?_⟩
  intro w
  have hw := hT (e0 w)
  simpa only [e0, e1, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.ofInjective_apply] using hw.symm

/-- Identity on the quotient and an injective restriction imply ambient injectivity. -/
theorem injective_of_identity_mod_subspace (U : Submodule F V) (f : V →ₗ[F] V)
    (T : U ≃ₗ[F] U)
    (hres : ∀ u : U, f u = (T u : V))
    (hmod : ∀ v, f v - v ∈ U) : Function.Injective f := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro v hv
  change v = 0
  have hv0 : f v = 0 := hv
  have hvU : v ∈ U := by
    have hm := U.neg_mem (hmod v)
    simpa only [hv0, zero_sub, neg_neg] using hm
  have hTu : T ⟨v, hvU⟩ = 0 := by
    apply Subtype.ext
    exact (hres ⟨v, hvU⟩).symm.trans hv0
  have hu : (⟨v, hvU⟩ : U) = 0 := T.injective (by simpa using hTu)
  exact congrArg Subtype.val hu

/-- Two embeddings agreeing modulo `U` extend to a single ambient automorphism
which induces the identity on `V / U`. -/
theorem exists_nearby_automorphism [FiniteDimensional F V]
    (U : Submodule F V) (X0 X1 : W →ₗ[F] V)
    (h0 : Function.Injective X0) (h1 : Function.Injective X1)
    (hU : ∀ w, X1 w - X0 w ∈ U) :
    ∃ S : V ≃ₗ[F] V, S.toLinearMap.comp X0 = X1 ∧ ∀ v, S v - v ∈ U := by
  classical
  let K := U.comap X0
  let x0 : K →ₗ[F] U := (X0.comp K.subtype).codRestrict U (fun w => w.property)
  let x1 : K →ₗ[F] U := (X1.comp K.subtype).codRestrict U (fun w => by
    have hw : X0 w ∈ U := w.property
    simpa only [sub_add_cancel, LinearMap.comp_apply, Submodule.coe_subtype]
      using U.add_mem (hU w) hw)
  have hx0 : Function.Injective x0 := by
    intro a b hab
    apply Subtype.ext
    apply h0
    exact congrArg Subtype.val hab
  have hx1 : Function.Injective x1 := by
    intro a b hab
    apply Subtype.ext
    apply h1
    exact congrArg Subtype.val hab
  obtain ⟨T, hT⟩ := exists_automorphism_map_embeddings x0 x1 hx0 hx1
  obtain ⟨r, hr⟩ := U.subtype.exists_leftInverse_of_injective U.ker_subtype
  let J : V →ₗ[F] V := LinearMap.id +
    U.subtype.comp ((T.toLinearMap - LinearMap.id).comp r)
  have hJres (u : U) : J u = (T u : V) := by
    have hru : r (u : V) = u := LinearMap.congr_fun hr u
    change (u : V) + ((T (r u) - r u : U) : V) = (T u : V)
    rw [hru]
    simp only [Submodule.coe_sub]
    abel
  have hJmod (v : V) : J v - v ∈ U := by
    change v + ((T (r v) - r v : U) : V) - v ∈ U
    simpa only [add_sub_cancel_left] using (T (r v) - r v).property
  let D : W →ₗ[F] U := (X1 - J.comp X0).codRestrict U (fun w => by
    change X1 w - J (X0 w) ∈ U
    convert U.sub_mem (hU w) (hJmod (X0 w)) using 1
    abel)
  let f : W →ₗ[F] V ⧸ U := U.mkQ.comp X0
  have hker : LinearMap.ker f ≤ LinearMap.ker D := by
    intro w hw
    have hwU : X0 w ∈ U := by
      have hh : X0 w ∈ LinearMap.ker U.mkQ := hw
      simpa only [Submodule.ker_mkQ] using hh
    change D w = 0
    apply Subtype.ext
    change X1 w - J (X0 w) = 0
    apply sub_eq_zero.mpr
    have ht := congrArg Subtype.val (hT (⟨w, hwU⟩ : K))
    have hj := hJres (x0 (⟨w, hwU⟩ : K))
    exact ht.symm.trans hj.symm
  obtain ⟨d, hd⟩ := exists_factor_of_ker_le f D hker
  let L : V →ₗ[F] V := J + U.subtype.comp (d.comp U.mkQ)
  have hLres (u : U) : L u = (T u : V) := by
    have hqu : U.mkQ (u : V) = 0 := by
      have hu : (u : V) ∈ LinearMap.ker U.mkQ := by
        simpa only [Submodule.ker_mkQ] using u.property
      exact hu
    simp only [L, LinearMap.add_apply, LinearMap.comp_apply, hqu, map_zero,
      add_zero, hJres]
  have hLmod (v : V) : L v - v ∈ U := by
    convert U.add_mem (hJmod v) (d (U.mkQ v)).property using 1
    simp only [L, LinearMap.add_apply, LinearMap.comp_apply, Submodule.coe_subtype]
    abel
  have hLi : Function.Injective L := injective_of_identity_mod_subspace U L T hLres hLmod
  let S : V ≃ₗ[F] V := LinearEquiv.ofInjectiveEndo L hLi
  refine ⟨S, ?_, ?_⟩
  · apply LinearMap.ext
    intro w
    have hdw := congrArg Subtype.val (LinearMap.congr_fun hd w)
    change J (X0 w) + (d (U.mkQ (X0 w)) : V) = X1 w
    change (d (U.mkQ (X0 w)) : V) = X1 w - J (X0 w) at hdw
    rw [hdw]
    abel
  · exact hLmod

/-- A linear map with image in another map's range lifts through that map. -/
theorem exists_lift_of_range_mem (g : Z →ₗ[F] V) (f : W →ₗ[F] V)
    (h : ∀ w, f w ∈ LinearMap.range g) :
    ∃ d : W →ₗ[F] Z, g.comp d = f := by
  classical
  obtain ⟨s, hs⟩ := g.rangeRestrict.exists_rightInverse_of_surjective g.range_rangeRestrict
  let f0 : W →ₗ[F] LinearMap.range g := f.codRestrict (LinearMap.range g) h
  refine ⟨s.comp f0, ?_⟩
  apply LinearMap.ext
  intro w
  have hw := congrArg Subtype.val (LinearMap.congr_fun hs (f0 w))
  exact hw

/-- The ambient extension may have its displacement factored through the exact
difference of the two embeddings. -/
theorem exists_nearby_embedding_factor [FiniteDimensional F V]
    (X0 X1 : W →ₗ[F] V) (h0 : Function.Injective X0) (h1 : Function.Injective X1) :
    ∃ (S : V ≃ₗ[F] V) (D : V →ₗ[F] W),
      S.toLinearMap.comp X0 = X1 ∧
        S.toLinearMap - LinearMap.id = (X1 - X0).comp D := by
  obtain ⟨S, hS, hmod⟩ := exists_nearby_automorphism (LinearMap.range (X1 - X0))
    X0 X1 h0 h1 (fun w => LinearMap.mem_range_self (X1 - X0) w)
  obtain ⟨D, hD⟩ := exists_lift_of_range_mem (X1 - X0)
    (S.toLinearMap - LinearMap.id) hmod
  exact ⟨S, D, hS, hD.symm⟩

end MatCP1Converse
