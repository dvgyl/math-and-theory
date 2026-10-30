module

public import MatCP1.Compression
public import MatCP1Converse.NearbySurjection

@[expose] public section

namespace MatCP1Converse

variable {F I U V W X : Type*} [Field F]
  [AddCommGroup U] [Module F U] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup X] [Module F X]
  [FiniteDimensional F U] [FiniteDimensional F V]
  [FiniteDimensional F W] [FiniteDimensional F X]

/-- Complete the actual row and column compression maps to ambient
automorphisms in the prescribed product spaces. -/
theorem exists_extend_compression_maps
    (p : (W × X) →ₗ[F] W) (q : U →ₗ[F] (U × V))
    (hp : Function.Surjective p) (hq : Function.Injective q) :
    ∃ (P : (W × X) ≃ₗ[F] (W × X)) (Q : (U × V) ≃ₗ[F] (U × V)),
      (LinearMap.fst F W X).comp P.toLinearMap = p ∧
      Q.toLinearMap.comp (LinearMap.inl F U V) = q := by
  obtain ⟨P, hP, _⟩ := exists_automorphism_fixed_subspace
    (⊥ : Submodule F (W × X)) p (LinearMap.fst F W X) hp
    (fun w => ⟨(w, 0), rfl⟩) (by
      intro v hv
      have hv0 : v = 0 := by simpa using hv
      simp [hv0])
  obtain ⟨Q, hQ⟩ := exists_automorphism_map_embeddings (LinearMap.inl F U V) q
    (fun _ _ h => congrArg Prod.fst h) hq
  refine ⟨P, Q, hP, ?_⟩
  apply LinearMap.ext
  exact hQ

/-- A simultaneous compression is an actual corner of a strictly equivalent
completion, with the same constant equivalences for every family member. -/
theorem jointCompression_exists_strict_completion
    (A : I → U →ₗ[F] W) (B : I → (U × V) →ₗ[F] (W × X))
    (h : MatCP1.JointCompression A B) :
    ∃ (M : I → (U × V) →ₗ[F] (W × X))
      (P : (W × X) ≃ₗ[F] (W × X)) (Q : (U × V) ≃ₗ[F] (U × V)),
      (∀ i, (LinearMap.fst F W X).comp ((M i).comp (LinearMap.inl F U V)) = A i) ∧
      ∀ i, M i = P.toLinearMap.comp ((B i).comp Q.toLinearMap) := by
  obtain ⟨p, q, hp, hq, hpq⟩ := h
  obtain ⟨P, Q, hP, hQ⟩ := exists_extend_compression_maps p q hp hq
  let M := fun i => P.toLinearMap.comp ((B i).comp Q.toLinearMap)
  refine ⟨M, P, Q, ?_, fun _ => rfl⟩
  intro i
  change ((LinearMap.fst F W X).comp P.toLinearMap).comp
    ((B i).comp (Q.toLinearMap.comp (LinearMap.inl F U V))) = A i
  rw [hP, hQ]
  exact hpq i

end MatCP1Converse
