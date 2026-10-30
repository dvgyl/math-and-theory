module

public import MatCP1Converse.NearbyEmbedding
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

namespace MatCP1Converse

variable {F V W Z : Type*} [Field F]
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
  [AddCommGroup Z] [Module F Z]

/-- Dual extension theorem: two surjections agreeing on a subspace are intertwined
by an ambient automorphism which fixes that subspace pointwise. -/
theorem exists_automorphism_fixed_subspace [FiniteDimensional F V]
    (K : Submodule F V) (Y0 Y1 : V →ₗ[F] W)
    (h0 : Function.Surjective Y0) (h1 : Function.Surjective Y1)
    (hK : ∀ v ∈ K, Y1 v = Y0 v) :
    ∃ T : V ≃ₗ[F] V, Y1.comp T.toLinearMap = Y0 ∧ ∀ v ∈ K, T v = v := by
  classical
  have hU (φ : Module.Dual F W) : Y0.dualMap φ - Y1.dualMap φ ∈ K.dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro v hv
    simp only [LinearMap.sub_apply, LinearMap.dualMap_apply, hK v hv, sub_self]
  obtain ⟨S, hS, hmod⟩ := exists_nearby_automorphism K.dualAnnihilator
    Y1.dualMap Y0.dualMap
    (LinearMap.dualMap_injective_of_surjective h1)
    (LinearMap.dualMap_injective_of_surjective h0) hU
  let T : V ≃ₗ[F] V := (Module.evalEquiv F V).trans
    (S.dualMap.trans (Module.evalEquiv F V).symm)
  have hT (v : V) (φ : Module.Dual F V) : φ (T v) = S φ v := by
    simp [T]
  refine ⟨T, ?_, ?_⟩
  · apply LinearMap.ext
    intro v
    apply Module.eval_apply_injective F
    apply LinearMap.ext
    intro φ
    change φ (Y1 (T v)) = φ (Y0 v)
    have hsφ := congrArg (fun ψ : Module.Dual F V => ψ v) (LinearMap.congr_fun hS φ)
    exact (hT v (Y1.dualMap φ)).trans hsφ
  · intro v hv
    apply Module.eval_apply_injective F
    apply LinearMap.ext
    intro φ
    change φ (T v) = φ v
    rw [hT]
    have hm := (Submodule.mem_dualAnnihilator _).mp (hmod φ) v hv
    exact sub_eq_zero.mp hm

/-- If the difference of two surjections factors through `R`, an intertwining
automorphism can be chosen whose displacement also factors through that exact map. -/
theorem exists_nearby_surjection_factor [FiniteDimensional F V]
    (Y0 Y1 : V →ₗ[F] W) (R : V →ₗ[F] Z)
    (h0 : Function.Surjective Y0) (h1 : Function.Surjective Y1)
    (hker : LinearMap.ker R ≤ LinearMap.ker (Y1 - Y0)) :
    ∃ (T : V ≃ₗ[F] V) (D : Z →ₗ[F] V),
      Y1.comp T.toLinearMap = Y0 ∧ T.toLinearMap - LinearMap.id = D.comp R := by
  obtain ⟨T, hT, hfix⟩ := exists_automorphism_fixed_subspace (LinearMap.ker R)
    Y0 Y1 h0 h1 (fun v hv => sub_eq_zero.mp (hker hv))
  have hkerT : LinearMap.ker R ≤ LinearMap.ker (T.toLinearMap - LinearMap.id) := by
    intro v hv
    change T v - v = 0
    rw [hfix v hv, sub_self]
  obtain ⟨D, hD⟩ := exists_factor_of_ker_le R (T.toLinearMap - LinearMap.id) hkerT
  exact ⟨T, D, hT, hD.symm⟩

end MatCP1Converse
