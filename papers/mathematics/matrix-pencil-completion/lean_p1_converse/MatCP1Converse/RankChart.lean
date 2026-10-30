module

public import MatCP1Converse.CommonChart
public import Mathlib.LinearAlgebra.Dimension.Free

@[expose] public section

namespace MatCP1Converse

section Factor

variable {F V W Z : Type*} [Field F]
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
  [AddCommGroup Z] [Module F Z]
  [FiniteDimensional F V] [FiniteDimensional F W]

/-- A rank factorization through any finite space of the actual rank, with the
injection and surjection both proved. -/
theorem exists_full_rank_factorization
    (H : W →ₗ[F] Z)
    (hRank : Module.finrank F (LinearMap.range H) = Module.finrank F V) :
    ∃ (U : V →ₗ[F] Z) (Q : W →ₗ[F] V),
      Function.Injective U ∧ Function.Surjective Q ∧ U.comp Q = H := by
  classical
  let e : V ≃ₗ[F] LinearMap.range H := LinearEquiv.ofFinrankEq _ _ hRank.symm
  let U := (LinearMap.range H).subtype.comp e.toLinearMap
  let Q := e.symm.toLinearMap.comp H.rangeRestrict
  refine ⟨U, Q, Subtype.val_injective.comp e.injective, ?_, ?_⟩
  · exact e.symm.surjective.comp (LinearMap.range_eq_top.mp H.range_rangeRestrict)
  · apply LinearMap.ext
    intro x
    simp [U, Q]

end Factor

section Chart

variable {F V W Z : Type*} [Field F] [Infinite F]
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
  [AddCommGroup Z] [Module F Z]
  [FiniteDimensional F V] [FiniteDimensional F W]

/-- Two maps of rank `dim V` have a common pair of graph coordinates making
their `V`-by-`V` blocks invertible. This uses the actual rank equalities, with no
assumed common nonsingular minor or rank factorization. -/
theorem exists_common_rank_chart
    (H0 H1 : (V × W) →ₗ[F] (V × Z))
    (h0 : Module.finrank F (LinearMap.range H0) = Module.finrank F V)
    (h1 : Module.finrank F (LinearMap.range H1) = Module.finrank F V) :
    ∃ (u : Z →ₗ[F] V) (v : V →ₗ[F] W),
      Function.Bijective
        ((LinearMap.id.coprod u).comp (H0.comp (LinearMap.id.prod v))) ∧
      Function.Bijective
        ((LinearMap.id.coprod u).comp (H1.comp (LinearMap.id.prod v))) := by
  obtain ⟨U0, Q0, hU0, hQ0, hF0⟩ := exists_full_rank_factorization H0 h0
  obtain ⟨U1, Q1, hU1, hQ1, hF1⟩ := exists_full_rank_factorization H1 h1
  let fst := LinearMap.fst F V Z
  let snd := LinearMap.snd F V Z
  have hprod (U : V →ₗ[F] (V × Z)) :
      (fst.comp U).prod (snd.comp U) = U := by
    apply LinearMap.ext
    intro x
    rfl
  have hU0' : Function.Injective ((fst.comp U0).prod (snd.comp U0)) := by
    rw [hprod]
    exact hU0
  have hU1' : Function.Injective ((fst.comp U1).prod (snd.comp U1)) := by
    rw [hprod]
    exact hU1
  obtain ⟨u, hu0, hu1⟩ := exists_common_invertible_graph
    (fst.comp U0) (fst.comp U1) (snd.comp U0) (snd.comp U1) hU0' hU1'
  let inl := LinearMap.inl F V W
  let inr := LinearMap.inr F V W
  have hQ0' : Function.Surjective ((Q0.comp inl).coprod (Q0.comp inr)) := by
    simpa only [inl, inr, LinearMap.coprod_comp_inl_inr] using hQ0
  have hQ1' : Function.Surjective ((Q1.comp inl).coprod (Q1.comp inr)) := by
    simpa only [inl, inr, LinearMap.coprod_comp_inl_inr] using hQ1
  obtain ⟨v, hv0, hv1⟩ := exists_common_invertible_cograph
    (Q0.comp inl) (Q1.comp inl) (Q0.comp inr) (Q1.comp inr) hQ0' hQ1'
  have heq (H : (V × W) →ₗ[F] (V × Z)) (U : V →ₗ[F] (V × Z))
      (Q : (V × W) →ₗ[F] V) (hF : U.comp Q = H) :
      (LinearMap.id.coprod u).comp (H.comp (LinearMap.id.prod v)) =
        (fst.comp U + u.comp (snd.comp U)).comp
          (Q.comp inl + (Q.comp inr).comp v) := by
    rw [← hF]
    apply LinearMap.ext
    intro x
    change (U (Q (x, v x))).1 + u ((U (Q (x, v x))).2) =
      (U (Q (x, 0) + Q (0, v x))).1 + u ((U (Q (x, 0) + Q (0, v x))).2)
    rw [← map_add]
    have hp : ((x, 0) + (0, v x) : V × W) = (x, v x) := by ext <;> simp
    rw [hp]
  refine ⟨u, v, ?_, ?_⟩
  · rw [heq H0 U0 Q0 hF0]
    exact hu0.comp hv0
  · rw [heq H1 U1 Q1 hF1]
    exact hu1.comp hv1

end Chart
end MatCP1Converse
