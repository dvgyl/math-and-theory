module

public import MatCP1Converse.NearbyEmbedding
public import MatCP1Converse.NearbySurjection
public import MatCP1.GenericRank

@[expose] public section

namespace MatCP1Converse

variable {F V W : Type*} [Field F]
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

/-- A full column map into `V × W` has an invertible graph compression to `V`.
This is a genuine existence statement; no nonsingular graph is assumed. -/
theorem exists_invertible_graph [FiniteDimensional F V]
    (a : V →ₗ[F] V) (b : V →ₗ[F] W)
    (hab : Function.Injective (a.prod b)) :
    ∃ u : W →ₗ[F] V, Function.Bijective (a + u.comp b) := by
  classical
  let K := LinearMap.ker b
  have hak : Function.Injective (a.comp K.subtype) := by
    intro x y hxy
    apply Subtype.ext
    apply hab
    apply Prod.ext
    · exact hxy
    · exact x.property.trans y.property.symm
  obtain ⟨T, hT⟩ := exists_automorphism_map_embeddings K.subtype (a.comp K.subtype)
    Subtype.val_injective hak
  have hk : LinearMap.ker b ≤ LinearMap.ker (T.toLinearMap - a) := by
    intro x hx
    change T x - a x = 0
    exact sub_eq_zero.mpr (hT ⟨x, hx⟩)
  obtain ⟨u, hu⟩ := exists_factor_of_ker_le b (T.toLinearMap - a) hk
  refine ⟨u, ?_⟩
  have heq : a + u.comp b = T.toLinearMap := by rw [hu]; abel
  rw [heq]
  exact T.bijective

/-- Over an infinite field one graph compression works simultaneously for two
full column maps. Each endpoint's existence is proved, rather than assumed. -/
theorem exists_common_invertible_graph [Infinite F] [FiniteDimensional F V]
    (a0 a1 : V →ₗ[F] V) (b0 b1 : V →ₗ[F] W)
    (h0 : Function.Injective (a0.prod b0))
    (h1 : Function.Injective (a1.prod b1)) :
    ∃ u : W →ₗ[F] V,
      Function.Bijective (a0 + u.comp b0) ∧
      Function.Bijective (a1 + u.comp b1) := by
  obtain ⟨u0, hu0⟩ := exists_invertible_graph a0 b0 h0
  obtain ⟨u1, hu1⟩ := exists_invertible_graph a1 b1 h1
  have hz0 : Function.Bijective
      ((a0 + u0.comp b0) + (0 : F) • ((u1 - u0).comp b0)) := by
    simpa using hu0
  have hz1 : Function.Bijective
      ((a1 + u0.comp b1) + (1 : F) • ((u1 - u0).comp b1)) := by
    have heq : (a1 + u0.comp b1) + (1 : F) • ((u1 - u0).comp b1) =
        a1 + u1.comp b1 := by
      simp only [one_smul, LinearMap.sub_comp]
      abel
    rw [heq]
    exact hu1
  obtain ⟨z, hz0, hz1⟩ :=
    ((MatCP1.eventually_bijective_affine
      (a0 + u0.comp b0) ((u1 - u0).comp b0) 0 hz0).and
      (MatCP1.eventually_bijective_affine
      (a1 + u0.comp b1) ((u1 - u0).comp b1) 1 hz1)).exists
  refine ⟨u0 + z • (u1 - u0), ?_, ?_⟩
  · simpa only [LinearMap.add_comp, LinearMap.smul_comp, add_assoc] using hz0
  · simpa only [LinearMap.add_comp, LinearMap.smul_comp, add_assoc] using hz1

/-- Dual form of the shared graph lemma, for full row maps. -/
theorem exists_common_invertible_cograph [Infinite F]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (a0 a1 : V →ₗ[F] V) (b0 b1 : W →ₗ[F] V)
    (h0 : Function.Surjective (a0.coprod b0))
    (h1 : Function.Surjective (a1.coprod b1)) :
    ∃ v : V →ₗ[F] W,
      Function.Bijective (a0 + b0.comp v) ∧
      Function.Bijective (a1 + b1.comp v) := by
  classical
  have hinj (a : V →ₗ[F] V) (b : W →ₗ[F] V)
      (h : Function.Surjective (a.coprod b)) :
      Function.Injective (a.dualMap.prod b.dualMap) := by
    intro φ ψ heq
    apply LinearMap.dualMap_injective_of_surjective h
    apply LinearMap.ext
    rintro ⟨x, y⟩
    have hx := congrArg (fun f : Module.Dual F V => f x) (congrArg Prod.fst heq)
    have hy := congrArg (fun f : Module.Dual F W => f y) (congrArg Prod.snd heq)
    simpa using congrArg₂ (fun r s : F => r + s) hx hy
  obtain ⟨u, hu0, hu1⟩ := exists_common_invertible_graph
    a0.dualMap a1.dualMap b0.dualMap b1.dualMap
    (hinj a0 b0 h0) (hinj a1 b1 h1)
  let v : V →ₗ[F] W := (Module.evalEquiv F W).symm.toLinearMap.comp
    (u.dualMap.comp (Module.evalEquiv F V).toLinearMap)
  have hv (x : V) (φ : Module.Dual F W) : φ (v x) = u φ x := by
    simp [v]
  have hdual (a : V →ₗ[F] V) (b : W →ₗ[F] V) :
      (a + b.comp v).dualMap = a.dualMap + u.comp b.dualMap := by
    ext φ x
    change φ (a x + b (v x)) = φ (a x) + u (b.dualMap φ) x
    rw [map_add]
    exact congrArg (fun z => φ (a x) + z) (hv x (b.dualMap φ))
  refine ⟨v, ?_, ?_⟩
  · apply LinearMap.dualMap_bijective_iff.mp
    rw [hdual]
    exact hu0
  · apply LinearMap.dualMap_bijective_iff.mp
    rw [hdual]
    exact hu1

end MatCP1Converse
