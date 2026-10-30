module

public import MatCP1.Cancellation

@[expose] public section

namespace MatCP1Converse

variable {F I U W V X : Type*} [Field F] [Infinite F]
  [AddCommGroup U] [Module F U] [AddCommGroup W] [Module F W]
  [AddCommGroup V] [Module F V] [AddCommGroup X] [Module F X]
  [FiniteDimensional F U] [FiniteDimensional F W]
  [FiniteDimensional F V] [FiniteDimensional F X]

/-- Actual equal-size-family strict cancellation in linear-map form. The result
returns constant ambient linear equivalences and does not invoke canonical forms. -/
theorem linear_strict_common_summand_cancellation
    (A B : I → U →ₗ[F] W) (S : I → V →ₗ[F] X)
    (P : (W × X) ≃ₗ[F] (W × X)) (Q : (U × V) ≃ₗ[F] (U × V))
    (hPQ : ∀ i, P.toLinearMap.comp (((B i).prodMap (S i)).comp Q.toLinearMap) =
      (A i).prodMap (S i)) :
    ∃ (p : W ≃ₗ[F] W) (q : U ≃ₗ[F] U),
      ∀ i, p.toLinearMap.comp ((B i).comp q.toLinearMap) = A i := by
  have h : MatCP1.JointCompression (fun i => (A i).prodMap (S i))
      (fun i => (B i).prodMap (S i)) :=
    ⟨P.toLinearMap, Q.toLinearMap, P.surjective, Q.injective, hPQ⟩
  obtain ⟨p, q, hp, hq, hpq⟩ := MatCP1.jointCompression_cancel_common_summand A B S h
  exact ⟨LinearEquiv.ofBijective p ⟨LinearMap.injective_iff_surjective.mpr hp, hp⟩,
    LinearEquiv.ofBijective q ⟨hq, LinearMap.injective_iff_surjective.mp hq⟩, hpq⟩

end MatCP1Converse
