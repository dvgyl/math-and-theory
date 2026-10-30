module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Algebra.Module.Projective

@[expose] public section

namespace MatCP1

variable {F I VA WA VB WB VT WT : Type*} [Field F]
  [AddCommGroup VA] [Module F VA] [AddCommGroup WA] [Module F WA]
  [AddCommGroup VB] [Module F VB] [AddCommGroup WB] [Module F WB]
  [AddCommGroup VT] [Module F VT] [AddCommGroup WT] [Module F WT]

/-- Simultaneous compression uses the same full-row and full-column maps for every member. -/
def JointCompression (A : I → VA →ₗ[F] WA) (B : I → VB →ₗ[F] WB) : Prop :=
  ∃ (P : WB →ₗ[F] WA) (Q : VA →ₗ[F] VB),
    Function.Surjective P ∧ Function.Injective Q ∧
      ∀ i, P.comp ((B i).comp Q) = A i

variable {VA' WA' VB' WB' : Type*}
  [AddCommGroup VA'] [Module F VA'] [AddCommGroup WA'] [Module F WA']
  [AddCommGroup VB'] [Module F VB'] [AddCommGroup WB'] [Module F WB']

/-- Simultaneous compression is invariant under independent changes of coordinates. -/
theorem JointCompression.linearEquiv
    (A : I → VA →ₗ[F] WA) (B : I → VB →ₗ[F] WB)
    (eVA : VA ≃ₗ[F] VA') (eWA : WA ≃ₗ[F] WA')
    (eVB : VB ≃ₗ[F] VB') (eWB : WB ≃ₗ[F] WB')
    (h : JointCompression A B) :
    JointCompression
      (fun i => eWA.toLinearMap.comp ((A i).comp eVA.symm.toLinearMap))
      (fun i => eWB.toLinearMap.comp ((B i).comp eVB.symm.toLinearMap)) := by
  rcases h with ⟨P, Q, hP, hQ, hPQ⟩
  refine ⟨eWA.toLinearMap.comp (P.comp eWB.symm.toLinearMap),
    eVB.toLinearMap.comp (Q.comp eVA.symm.toLinearMap), ?_, ?_, ?_⟩
  · exact eWA.surjective.comp (hP.comp eWB.symm.surjective)
  · exact eVB.injective.comp (hQ.comp eVA.symm.injective)
  · intro i
    ext x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
    exact congrArg eWA (LinearMap.congr_fun (hPQ i) (eVA.symm x))

/-- A joint quotient of a joint subrepresentation supplies an actual constant compression. -/
theorem jointCompression_of_subquotient
    (A : I → VA →ₗ[F] WA) (B : I → VB →ₗ[F] WB)
    (T : I → VT →ₗ[F] WT)
    (rV : VT →ₗ[F] VB) (rW : WT →ₗ[F] WB)
    (pV : VT →ₗ[F] VA) (pW : WT →ₗ[F] WA)
    (hrV : Function.Injective rV) (hrW : Function.Injective rW)
    (hpV : Function.Surjective pV) (hpW : Function.Surjective pW)
    (hr : ∀ i, (B i).comp rV = rW.comp (T i))
    (hp : ∀ i, (A i).comp pV = pW.comp (T i)) :
    JointCompression A B := by
  classical
  obtain ⟨s, hs⟩ := pV.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hpV)
  obtain ⟨l, hl⟩ := rW.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hrW)
  refine ⟨pW.comp l, rV.comp s, ?_, ?_, ?_⟩
  · intro a
    obtain ⟨t, ht⟩ := hpW a
    refine ⟨rW t, ?_⟩
    have hlt : l (rW t) = t := LinearMap.congr_fun hl t
    simpa [LinearMap.comp_apply, hlt] using ht
  · intro a b hab
    have hsab : s a = s b := hrV hab
    have hsa : pV (s a) = a := LinearMap.congr_fun hs a
    have hsb : pV (s b) = b := LinearMap.congr_fun hs b
    exact hsa.symm.trans ((congrArg pV hsab).trans hsb)
  · intro i
    ext a
    change pW (l (B i (rV (s a)))) = A i a
    have hri := LinearMap.congr_fun (hr i) (s a)
    simp only [LinearMap.comp_apply] at hri
    rw [hri]
    have hlt := LinearMap.congr_fun hl (T i (s a))
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at hlt
    rw [hlt]
    have hpi := LinearMap.congr_fun (hp i) (s a)
    have hsa := LinearMap.congr_fun hs a
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at hsa
    simpa only [LinearMap.comp_apply, LinearMap.id_apply, hsa] using hpi.symm

variable {XS YS : Type*}
  [AddCommGroup XS] [Module F XS] [AddCommGroup YS] [Module F YS]

/-- A common kernel whose projection into `B` is injective and onto `A` yields compression. -/
theorem jointCompression_of_common_kernel
    (A : I → VA →ₗ[F] WA) (B : I → VB →ₗ[F] WB)
    (S : I → XS →ₗ[F] YS) (T : I → VT →ₗ[F] WT)
    (rV : VT →ₗ[F] VB) (rW : WT →ₗ[F] WB)
    (pV : VT →ₗ[F] VA) (pW : WT →ₗ[F] WA)
    (hV : VT →ₗ[F] XS) (hW : WT →ₗ[F] YS)
    (hrV : Function.Injective (rV.prod hV))
    (hrW : Function.Injective (rW.prod hW))
    (hpV : Function.Surjective (pV.prod hV))
    (hpW : Function.Surjective (pW.prod hW))
    (hr : ∀ i, (B i).comp rV = rW.comp (T i))
    (hp : ∀ i, (A i).comp pV = pW.comp (T i))
    (hh : ∀ i, (S i).comp hV = hW.comp (T i)) :
    JointCompression A B := by
  classical
  let TV := LinearMap.ker hV
  let TW := LinearMap.ker hW
  let TK (i : I) : TV →ₗ[F] TW :=
    { toFun := fun x => ⟨T i x, by
        change hW (T i x) = 0
        have hx : hV x = 0 := x.property
        have hi := LinearMap.congr_fun (hh i) (x : VT)
        simpa only [LinearMap.comp_apply, hx, map_zero] using hi.symm⟩
      map_add' := fun x y => by apply Subtype.ext; exact (T i).map_add x y
      map_smul' := fun a x => by apply Subtype.ext; exact (T i).map_smul a x }
  apply jointCompression_of_subquotient A B TK
    (rV.comp TV.subtype) (rW.comp TW.subtype)
    (pV.comp TV.subtype) (pW.comp TW.subtype)
  · intro x y hxy
    apply Subtype.ext
    apply hrV
    apply Prod.ext
    · exact hxy
    · exact x.property.trans y.property.symm
  · intro x y hxy
    apply Subtype.ext
    apply hrW
    apply Prod.ext
    · exact hxy
    · exact x.property.trans y.property.symm
  · intro a
    obtain ⟨v, hv⟩ := hpV (a, 0)
    have hv0 : hV v = 0 := congrArg Prod.snd hv
    exact ⟨⟨v, hv0⟩, congrArg Prod.fst hv⟩
  · intro a
    obtain ⟨v, hv⟩ := hpW (a, 0)
    have hv0 : hW v = 0 := congrArg Prod.snd hv
    exact ⟨⟨v, hv0⟩, congrArg Prod.fst hv⟩
  · intro i
    ext x
    exact LinearMap.congr_fun (hr i) (x : VT)
  · intro i
    ext x
    exact LinearMap.congr_fun (hp i) (x : VT)

end MatCP1
