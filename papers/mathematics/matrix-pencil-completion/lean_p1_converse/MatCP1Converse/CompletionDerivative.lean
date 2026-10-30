module

public import MatCP1Converse.CompletionNormalization

@[expose] public section

namespace MatCP1Converse

variable {F V W U : Type*} [Field F]
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
  [AddCommGroup U] [Module F U]

/-- The first-order coefficient induces a map from the zero-order kernel to
the zero-order cokernel. This is the actual derivative map used in completion. -/
def completionDerivative (A0 A1 : V →ₗ[F] W) :
    LinearMap.ker A0 →ₗ[F] W ⧸ LinearMap.range A0 :=
  (LinearMap.range A0).mkQ.comp (A1.comp (LinearMap.ker A0).subtype)

/-- A pencil strictly equivalent to `B(t) ⊕ t I` has derivative rank at least
the scalar-summand dimension. The witnessing injective map is constructed from
the given constant strict equivalence, not assumed as a derivative hypothesis. -/
theorem completion_derivative_rank_ge_scalar_summand
    [FiniteDimensional F U] [FiniteDimensional F V]
    (B0 B1 : U →ₗ[F] W)
    (M0 M1 : (U × V) →ₗ[F] (W × V))
    (P : (W × V) ≃ₗ[F] (W × V)) (Q : (U × V) ≃ₗ[F] (U × V))
    (h0 : M0 = P.toLinearMap.comp ((B0.prodMap (0 : V →ₗ[F] V)).comp Q.toLinearMap))
    (h1 : M1 = P.toLinearMap.comp ((B1.prodMap (LinearMap.id : V →ₗ[F] V)).comp Q.toLinearMap)) :
    Module.finrank F V ≤ Module.finrank F (LinearMap.range (completionDerivative M0 M1)) := by
  classical
  let j0 : V →ₗ[F] (U × V) := Q.symm.toLinearMap.comp (LinearMap.inr F U V)
  have hj0 (v : V) : j0 v ∈ LinearMap.ker M0 := by
    change M0 (j0 v) = 0
    rw [h0]
    simp [j0]
  let j : V →ₗ[F] LinearMap.ker M0 := j0.codRestrict (LinearMap.ker M0) hj0
  let d := completionDerivative M0 M1
  let f := d.comp j
  have hfi : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro v hv
    change v = 0
    have hq : M1 (j0 v) ∈ LinearMap.range M0 := by
      have hz : (LinearMap.range M0).mkQ (M1 (j0 v)) = 0 := hv
      exact (Submodule.Quotient.mk_eq_zero _).mp hz
    obtain ⟨w, hw⟩ := hq
    rw [h0, h1] at hw
    have hh := P.injective hw
    have hv0 := congrArg Prod.snd hh
    simpa [j0] using hv0.symm
  let f0 : V →ₗ[F] LinearMap.range d := f.codRestrict (LinearMap.range d)
    (fun v => ⟨j v, rfl⟩)
  have hf0 : Function.Injective f0 := by
    intro x y hxy
    exact hfi (congrArg Subtype.val hxy)
  exact LinearMap.finrank_le_finrank_of_injective hf0

end MatCP1Converse
